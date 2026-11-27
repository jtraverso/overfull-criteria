module

public import OverfullWork.ChenShanTheorem415
public import OverfullWork.ChenShanNestedIterationClosure
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical
universe u

private noncomputable def fiberEquivToUsed {X V C : Type*} (p : X → V) (q : X → C)
    (hq : Function.Injective (fun x => (p x,q x))) (v : V) :
    {x // p x = v} ≃ {c // ∃ x, p x = v ∧ q x = c} :=
  Equiv.ofBijective (fun x => ⟨q x.val,x.val,x.property,rfl⟩) ⟨
    fun x y h => Subtype.ext (hq (Prod.ext (x.property.trans y.property.symm)
      (congrArg Subtype.val h))),
    fun ⟨_,x,hp,hq'⟩ => ⟨⟨x,hp⟩,Subtype.ext hq'⟩⟩

private theorem swap_injective {X V C : Type*} {p : X → V} {q : X → C}
    (h : Function.Injective (fun x => (p x,q x))) :
    Function.Injective (fun x => (q x,p x)) :=
  fun _ _ he => h (congrArg Prod.swap he)

private theorem extend_with_exact_incidence {H X V W : Type*}
    (p : H → V) (q : X → V) (c : H → W) (d : X → W)
    (hd : Function.Injective (fun x => (q x,d x)))
    (hc : ∀ v w, (¬ ∃ x, q x = v ∧ d x = w) →
      ∃! e : H, p e = v ∧ c e = w)
    (hav : ∀ e : H, ¬ ∃ x, q x = p e ∧ d x = c e) :
    ∀ v w, ∃! e : H ⊕ X, Sum.elim p q e = v ∧ Sum.elim c d e = w := by
  intro v w
  by_cases h : ∃ x, q x = v ∧ d x = w
  · obtain ⟨x,hv,hw⟩ := h
    refine ⟨.inr x,⟨hv,hw⟩,?_⟩
    rintro (e | y) ⟨hv',hw'⟩
    · exact (hav e ⟨x,hv.trans hv'.symm,hw.trans hw'.symm⟩).elim
    · exact congrArg Sum.inr (hd (Prod.ext (hv'.trans hv.symm) (hw'.trans hw.symm)))
  · obtain ⟨e,he,hUnique⟩ := hc v w h
    refine ⟨.inl e,he,?_⟩
    rintro (f | x) hf
    · exact congrArg Sum.inl (hUnique f hf)
    · exact (h ⟨x,hf⟩).elim

/-- Chen–Shan, Theorem 4.16. The type X indexes the individual copies
of the precolored edges, including any parallel copies. The extended
coloring uses each color exactly once at every vertex. -/
theorem exists_regular_bipartite_precoloring_extension (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, ∃ m₀ : ℕ, 0 < ε₀ ∧
      ∀ m : ℕ, m₀ ≤ m →
      ∀ (A B W X : Type u) [Fintype A] [Fintype B] [Fintype W] [Fintype X]
        (E : A → B → Prop) (l : X → A) (r : X → B) (d : X → W),
      Fintype.card A = m → Fintype.card B = m →
      Function.Injective (fun x => (l x,d x)) →
      Function.Injective (fun x => (r x,d x)) →
      (∀ a, Fintype.card {b // E a b} + Fintype.card {x // l x = a} = Fintype.card W) →
      (∀ b, Fintype.card {a // E a b} + Fintype.card {x // r x = b} = Fintype.card W) →
      (∀ a, (1/2+η)*m ≤ ((univ.filter (E a)).card : ℝ)) →
      (∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => E a b)).card : ℝ)) →
      (∀ a, (Fintype.card {x // l x = a} : ℝ) ≤ ε₀*m) →
      (∀ b, (Fintype.card {x // r x = b} : ℝ) ≤ ε₀*m) →
      (∀ w, (Fintype.card {x // d x = w} : ℝ) ≤ ε₀*m) →
      let H := {p : A × B // E p.1 p.2}
      ∃ c : H ⊕ X → W, (∀ x, c (.inr x) = d x) ∧
        (∀ a w, ∃! e : H ⊕ X, Sum.elim (fun p => p.val.1) l e = a ∧ c e = w) ∧
        (∀ b w, ∃! e : H ⊕ X, Sum.elim (fun p => p.val.2) r e = b ∧ c e = w) := by
  obtain ⟨ε₀,m₀,hε,hDense⟩ := exists_triangle_decomposition_of_dense_tripartite.{u} η hη
  refine ⟨ε₀,m₀,hε,?_⟩
  intro m hm A B W X _ _ _ _ E l r d hA hB hl hr hRegA hRegB hMinA hMinB hMaxA hMaxB hMaxW H
  let L := fun a w => ∃ x, l x = a ∧ d x = w
  let R := fun b w => ∃ x, r x = b ∧ d x = w
  let _ : ∀ a w, Decidable (L a w) := fun _ _ => Classical.propDecidable _
  let _ : ∀ b w, Decidable (R b w) := fun _ _ => Classical.propDecidable _
  have hL (a) : Fintype.card {x // l x = a} = Fintype.card {w // L a w} :=
    Fintype.card_congr (fiberEquivToUsed l d hl a)
  have hR (b) : Fintype.card {x // r x = b} = Fintype.card {w // R b w} :=
    Fintype.card_congr (fiberEquivToUsed r d hr b)
  have hWL (w) : Fintype.card {x // d x = w} = Fintype.card {a // L a w} :=
    Fintype.card_congr ((fiberEquivToUsed d l (swap_injective hl) w).trans
      (Equiv.subtypeEquivRight (fun _ => exists_congr (fun _ => and_comm))))
  have hWR (w) : Fintype.card {x // d x = w} = Fintype.card {b // R b w} :=
    Fintype.card_congr ((fiberEquivToUsed d r (swap_injective hr) w).trans
      (Equiv.subtypeEquivRight (fun _ => exists_congr (fun _ => and_comm))))
  obtain ⟨C⟩ := residual_coloring_from_dense_decomposition E L R m η ε₀ hA hB
    (fun a => by rw [← hL]; exact hRegA a) (fun b => by rw [← hR]; exact hRegB b)
    (fun w => (hWL w).symm.trans (hWR w)) hMinA hMinB
    (fun a => by rw [← Fintype.card_subtype, ← hL]; exact hMaxA a)
    (fun b => by rw [← Fintype.card_subtype, ← hR]; exact hMaxB b)
    (fun w => by rw [← Fintype.card_subtype, ← hWL]; exact hMaxW w)
    (fun w => by rw [← Fintype.card_subtype, ← hWR]; exact hMaxW w)
    (hDense m hm ε₀ hε.le le_rfl A B W)
  have hLeft (a : A) (w : W) (hw : ¬ L a w) :
      ∃! e : H, e.val.1 = a ∧ C.color e = w := by
    obtain ⟨b,⟨hb,hc⟩,hOnly⟩ := C.coversLeft a w hw
    refine ⟨⟨(a,b),hb⟩,⟨rfl,hc⟩,?_⟩
    rintro ⟨⟨a',b'⟩,he⟩ ⟨rfl,he'⟩
    exact Subtype.ext (Prod.ext rfl (hOnly b' ⟨he,he'⟩))
  have hRight (b : B) (w : W) (hw : ¬ R b w) :
      ∃! e : H, e.val.2 = b ∧ C.color e = w := by
    obtain ⟨a,⟨ha,hc⟩,hOnly⟩ := C.coversRight b w hw
    refine ⟨⟨(a,b),ha⟩,⟨rfl,hc⟩,?_⟩
    rintro ⟨⟨a',b'⟩,he⟩ ⟨rfl,he'⟩
    exact Subtype.ext (Prod.ext (hOnly a' ⟨he,he'⟩) rfl)
  exact ⟨Sum.elim C.color d,fun _ => rfl,
    extend_with_exact_incidence (fun e : H => e.val.1) l C.color d hl hLeft
      (fun e => (C.available e).1),
    extend_with_exact_incidence (fun e : H => e.val.2) r C.color d hr hRight
      (fun e => (C.available e).2)⟩

end OverfullWork.ChenShan
