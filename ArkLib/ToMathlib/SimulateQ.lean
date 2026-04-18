import VCVio.OracleComp.SimSemantics.QueryImpl
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleComp

universe u v w

variable {ι : Type} {spec : OracleSpec ι} {α : Type u}
  {m : Type u → Type v} {n : Type u → Type w}
  [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  [MonadLiftT m n] [LawfulMonadLiftT m n]

@[simp]
lemma simulateQ_liftTarget (impl : QueryImpl spec m) (comp : OracleComp spec α) :
    simulateQ (impl.liftTarget n) comp = liftM (simulateQ impl comp) := by
  induction comp using OracleComp.inductionOn with
  | pure x => simp [liftM_pure]
  | query_bind t k ih => simp [ih, liftM_bind]
