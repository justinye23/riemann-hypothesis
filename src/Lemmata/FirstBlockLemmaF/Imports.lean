module

public import Mathlib.NumberTheory.Padics.Complex

@[expose] public section

namespace Bl.FirstBlockLemmaF

theorem goal1 :
  ∀ (p : Nat) [_hp : Fact (Nat.Prime p)] {a b : PadicComplex p} {c : Real},
  LE.le.{0} (Norm.norm.{0} a) c → LE.le.{0} (Norm.norm.{0} b) c → LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) c := by
  intro p _hp a b c ha hb
  simpa only [sub_eq_add_neg] using
    (IsUltrametricDist.norm_add_le_max a (-b)).trans
      (max_le ha (by simpa only [norm_neg] using hb))

end Bl.FirstBlockLemmaF
