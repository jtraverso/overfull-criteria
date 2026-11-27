module

public import OverfullWork.ChenShanTheorem416
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical
universe u

/-- Incidence in the graph outside the core. The edge index retains
parallel copies and can have both endpoints in any of the three parts. -/
def OutsideCoreIncident {V X : Type*} (p q : X → V) (x : X) (v : V) : Prop :=
  p x = v ∨ q x = v

def OutsideCoreUsesColor {V X W : Type*} (p q : X → V) (d : X → W)
    (v : V) (w : W) : Prop :=
  ∃ x, OutsideCoreIncident p q x v ∧ d x = w

private theorem exact_incidence_after_core_extension {H X W V : Type*}
    (core : H → V → Prop) (outside : X → V → Prop) (c : H → W) (d : X → W)
    (hProper : ∀ v w x y, outside x v → outside y v → d x = w → d y = w → x = y)
    (hAvailable : ∀ h v, core h v → ¬ ∃ x, outside x v ∧ d x = c h)
    (hCore : ∀ v w, (¬ ∃ x, outside x v ∧ d x = w) →
      ∃! h : H, core h v ∧ c h = w) :
    ∀ v w, ∃! e : H ⊕ X, Sum.elim (fun h => core h v) (fun x => outside x v) e ∧
      Sum.elim c d e = w := by
  intro v w
  by_cases hw : ∃ x, outside x v ∧ d x = w
  · obtain ⟨x,hx,hc⟩ := hw
    refine ⟨.inr x,⟨hx,hc⟩,?_⟩
    rintro (h | y) ⟨hy,hd⟩
    · exact (hAvailable h v hy ⟨x,hx,hc.trans hd.symm⟩).elim
    · exact congrArg Sum.inr (hProper v w y x hy hx hd hc)
  · obtain ⟨h,hh,hUnique⟩ := hCore v w hw
    refine ⟨.inl h,hh,?_⟩
    rintro (h' | x) he
    · exact congrArg Sum.inl (hUnique h' he)
    · exact (hw ⟨x,he⟩).elim

set_option maxHeartbeats 1600000 in
/-- The completion step of Chen–Shan, Theorem 4.2, given the balanced
coloring supplied by Lemma 3.9. In the available-color formulation, an
auxiliary matching enters only through its used endpoint sets. We use
those sets directly, keeping the original edge copies in the result. -/
theorem exists_factorization_of_balanced_outside_coloring (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ m₀ : ℕ, 0 < ε ∧
      ∀ m : ℕ, m₀ ≤ m →
      ∀ (A B Z W X : Type u) [Fintype A] [Fintype B] [Fintype W] [Fintype X]
        (E : A → B → Prop) (p q : X → A ⊕ (B ⊕ Z)) (d : X → W),
      let V := A ⊕ (B ⊕ Z)
      let out := OutsideCoreIncident p q
      let used := OutsideCoreUsesColor p q d
      Fintype.card A = m → Fintype.card B = m →
      (∀ a, (1/2+η)*m ≤ ((univ.filter (E a)).card : ℝ)) →
      (∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => E a b)).card : ℝ)) →
      (∀ a, Fintype.card {b // E a b} + Fintype.card {w // used (.inl a) w} =
        Fintype.card W) →
      (∀ b, Fintype.card {a // E a b} + Fintype.card {w // used (.inr (.inl b)) w} =
        Fintype.card W) →
      (∀ v w x y, out x v → out y v → d x = w → d y = w → x = y) →
      (∀ z w, used (.inr (.inr z)) w) →
      (∀ a, ((univ.filter (used (.inl a))).card : ℝ) ≤ ε*m) →
      (∀ b, ((univ.filter (used (.inr (.inl b)))).card : ℝ) ≤ ε*m) →
      (∀ w, Fintype.card {a // used (.inl a) w} =
        Fintype.card {b // used (.inr (.inl b)) w}) →
      (∀ w, ((univ.filter (fun a => used (.inl a) w)).card : ℝ) ≤ 2*ε*m+2) →
      let H := {ab : A × B // E ab.1 ab.2}
      ∃ c : H ⊕ X → W, (∀ x, c (.inr x) = d x) ∧
        ∀ v w, ∃! e : H ⊕ X,
          Sum.elim (fun h => (Sum.inl h.val.1 : V) = v ∨ .inr (.inl h.val.2) = v)
            (fun x => out x v) e ∧ c e = w := by
  obtain ⟨ε₁,N,hε₁,hDense⟩ := exists_triangle_decomposition_of_dense_tripartite.{u} η hη
  refine ⟨ε₁/4,max N ⌈4/ε₁⌉₊,by positivity,?_⟩
  intro m hm A B Z W X _ _ _ _ E p q d V out used hA hB hMinA hMinB
    hRegA hRegB hProper hZ hMaxA hMaxB hBal hMaxW H
  have hm' : N ≤ m := (le_max_left _ _).trans hm
  have hmScale : 4/ε₁ ≤ (m:ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right N ⌈4/ε₁⌉₊).trans hm)
  have hScale : 4 ≤ ε₁*m := by
    have h := (div_le_iff₀ hε₁).mp hmScale
    rwa [mul_comm] at h
  have hScaleA : ε₁/4*m ≤ ε₁*m := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith only [hε₁]
  have hScaleW : 2*(ε₁/4)*m+2 ≤ ε₁*m := by linarith only [hScale]
  let L := fun a w => used (.inl a) w
  let R := fun b w => used (.inr (.inl b)) w
  let _ : ∀ a w, Decidable (L a w) := fun _ _ => Classical.propDecidable _
  let _ : ∀ b w, Decidable (R b w) := fun _ _ => Classical.propDecidable _
  obtain ⟨C⟩ := residual_coloring_from_dense_decomposition E L R m η ε₁ hA hB
    hRegA hRegB hBal hMinA hMinB
    (fun a => (hMaxA a).trans hScaleA) (fun b => (hMaxB b).trans hScaleA)
    (fun w => (hMaxW w).trans hScaleW)
    (fun w => by
      have hw := (hMaxW w).trans hScaleW
      rw [← Fintype.card_subtype, ← hBal w, Fintype.card_subtype]
      exact hw)
    (hDense m hm' ε₁ hε₁.le le_rfl A B W)
  let core (h : H) (v : V) := (Sum.inl h.val.1 : V) = v ∨ .inr (.inl h.val.2) = v
  have hAvailable (h : H) (v : V) (hv : core h v) : ¬ used v (C.color h) := by
    rcases hv with rfl | rfl
    · exact (C.available h).1
    · exact (C.available h).2
  have hCover (v : V) (w : W) (hw : ¬ used v w) :
      ∃! h : H, core h v ∧ C.color h = w := by
    rcases v with a | (b | z)
    · obtain ⟨b,⟨hb,hc⟩,hUnique⟩ := C.coversLeft a w hw
      refine ⟨⟨(a,b),hb⟩,⟨Or.inl rfl,hc⟩,?_⟩
      rintro ⟨⟨a',b'⟩,he⟩ ⟨hv,he'⟩
      have ha : a' = a := by simpa [core] using hv
      subst a'
      exact Subtype.ext (Prod.ext rfl (hUnique b' ⟨he,he'⟩))
    · obtain ⟨a,⟨ha,hc⟩,hUnique⟩ := C.coversRight b w hw
      refine ⟨⟨(a,b),ha⟩,⟨Or.inr rfl,hc⟩,?_⟩
      rintro ⟨⟨a',b'⟩,he⟩ ⟨hv,he'⟩
      have hb : b' = b := by
        rcases hv with hv | hv
        · cases hv
        · exact Sum.inl.inj (Sum.inr.inj hv)
      subst b'
      exact Subtype.ext (Prod.ext (hUnique a' ⟨he,he'⟩) rfl)
    · exact (hw (hZ z w)).elim
  exact ⟨Sum.elim C.color d,fun _ => rfl,
    exact_incidence_after_core_extension core out C.color d hProper hAvailable hCover⟩

end OverfullWork.ChenShan
