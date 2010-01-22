module TestLDA where

import Decl
import Core
import MkCore
import qualified Conjugacy
import qualified UnLift
import qualified Math
import Type
import Code
import Simulate
import Data
import Control.Monad
import Control.Monad.State
import Parse
import System.IO.Unsafe
import Util
import GenC
import qualified Data.Map as M
import Marginalize
import CodeOpt

-- -------------------------------------------------------------------------------
-- | Define the LDA model
ldaMOD = 
  MOD [ DECL (LHS "alpha"    []) (RHS "Gam"    [CONST (REAL 1), CONST (REAL 1)] []) []
      , DECL (LHS "eta"      []) (RHS "Gam"    [CONST (REAL 1), CONST (REAL 1)] []) []
      , DECL (LHS "beta"  ["k"]) (RHS "DirSym" [VAR "eta"  , VAR "V"] []) [RANGE "k" (CONST (INT 1)) (VAR "K")]
      , DECL (LHS "theta" ["d"]) (RHS "DirSym" [VAR "alpha", VAR "K"] []) [RANGE "d" (CONST (INT 1)) (VAR "D")]
      , DECL (LHS "z" ["d","n"]) (RHS "Mult"   [IND ("theta") [VAR "d"]] [])                         [RANGE "d" (CONST (INT 1)) (VAR "D"), RANGE "n" (CONST (INT 1)) (IND ("N") [VAR "d"])]
      , DECL (LHS "w" ["d","n"]) (RHS "Mult"   [IND ("beta") [IND ("z") [VAR "d", VAR "n"]]] [])     [RANGE "d" (CONST (INT 1)) (VAR "D"), RANGE "n" (CONST (INT 1)) (IND ("N") [VAR "d"])]
      ]

ldacMOD =unsafePerformIO (loadHier "LDA.hier")
mixMOD  = unsafePerformIO (loadHier "mix_gauss.hier")
hmmMOD  = unsafePerformIO (loadHier "HMM.hier")
hallMOD = unsafePerformIO (loadHier "hallM.hier")
hypMOD  = unsafePerformIO (loadHier "hyp.hier")
lda2MOD = unsafePerformIO (loadHier "LDA2.hier")
m1MOD = unsafePerformIO (loadHier "IBMmodel1.hier")
bqfsMOD = unsafePerformIO (loadHier "BQFS.hier")
undMOD = unsafePerformIO (loadHier "underlying.hier")

(modMOD,_) = m1MOD
modDecl = let MOD decls = modMOD in decls!!7
modMOD1 = MOD [modDecl]

(modCore,modType0) = filterTypeDefinitions $ mkCore modMOD
modCore' = nameSPVars $ UnLift.simplify modCore
modCore'' = inferMissingRanges (getTypeMap modType0 modCore') modCore'

modPrior = Math.simplify $ coreToPrior modCore''
modLik   = removeSubF $ makeLikFunction modPrior (getGlobals modCore'') (getTypeMap modType0 modCore'')
modInit  = removeSub [makeInitializeFunction modPrior d typ | d <- decls modPrior]
  where typ = getTypeMap modType0 modPrior
modDump  = removeSub [makeDumpFunction modPrior d typ | d <- decls modPrior]
  where typ = getTypeMap modType0 modPrior

modConj  = unliftCoreE $ unliftCore $ fixOffsets $ Math.simplify $ UnLift.simplify $ nameSPVars $ Conjugacy.simplify modCore
modType  = getTypeMap modType0 modConj

(modMarg, modType', updates) = -- (modConj, modType, [])
  let (tm', _, mod', upd) = marginalizeDirichlet modType "tt"  modConj
--      (tm'',_, mod'',upd')= marginalizeDirichlet tm'     "theta" mod'
  in  (mod', tm', upd)

modSamp  = [makeSampleFunction d modType' updates False | d <- decls $ unliftCore modMarg]
modSamp' = removeSub $ removeID modSamp


--genCPPF = devectorizeF modType . mapReturnType
--genC0   = GenC 0 modType M.empty

-- evalStateT (mapM_ (genF . head . giveNewVarNames M.empty . (:[]) . devectorizeF . mapReturnType) modSamp') (GenC 0 modType M.empty)
-- evalStateT (mapM_ (genF . genCPPF) modSamp') genC0
-- evalStateT (gen (genCPPF modLik) (map genCPPF modInit) (map genCPPF modSamp') []) genC0

{-
runMOD = runM Quiet $ do
  (w,_V,[_D,_N]) <- lift (loadDiscrete "\n" "testW")
  simAll 50 modLik modInit modSamp
     [("w",w), ("D",_D), ("N",_N), ("V",_V), ("K",II 2), ("eta",RR 0.1), ("alpha",RR 0.1)]
-}

{-

output in C should be something like:

void resample_theta_d(float*theta_d, float alpha, int*z_d, int N_d, int K)
  int n,k;
  float* post = (float*) malloc(K * sizeof(float));
  for (k=0; k<K; k++) {
    post[k] = 0;
  }
  for (n=0; n<N_d; n++) {
    post[z_d[n]]++;
  }
  for (k=0; k<K; k++) {
    post[k] += alpha;
  }
  randdir(theta_d, post);
  delete(post);
}

output in Java should be something like:

  static void ressample_theta_d(float[]theta_d, float alpha, int[]z_d, int N_d, int K) {
    float[] post = new float[K];
    for (int k=0; k<K; k++) {
      post[k] = 0;
    }
    for (int n=0; n<N_d; n++) {
      post[z_d[n]]++;
    }
    for (int k=0; k<K; k++) {
      post[k] += alpha;
    }
    randdir(theta_d, post)
  }

output in matlab should be something like:

function theta_d = resample_theta_d(theta_d, alpha, z_d, N_d, K)
post = zeros(1,K);
for n=1:N_d,
  post(z_d(n)) = post(z_d(n)) + 1;
end;
post = post + alpha;
theta_d = randdir(post)


finally, output in Haskell should be something like:

resample_theta_d theta_d alpha z_d _N_d _K = do
  post <- newArray (1,_K) 0
  mapM_ [1.._N_d] $ \n -> do
    z_d_n <- readArray post n
    writeArray post z_d_n . (+1) =<< readArray post z_d_n
  mapM_ [1.._K] $ \k -> do
    writeArray post k (+alpha) =<< readArray post k
  randdir theta_d post
-}
