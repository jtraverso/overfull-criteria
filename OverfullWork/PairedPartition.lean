module

public import OverfullWork.SigningMoments
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section


/-!
# Balanced partitions separating prescribed pairs

Every signing of a fixed pairing selects one vertex per pair. Sixth-moment
averaging supplies a signing controlling all rows of a bounded matrix.
The pairing carries no degree-control or colouring hypothesis.
-/

namespace OverfullWork.PairedPartition

open Finset SigningMoments
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

def part (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) : Finset V :=
  univ.image (fun i => e (i,s i))

omit [Fintype V] [DecidableEq V] in
theorem select_injective (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) :
    Function.Injective (fun i => e (i,s i)) := by
  intro i j h
  exact congrArg Prod.fst (e.injective h)

omit [Fintype V] in
theorem card_part (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) :
    (part e s).card = m := by
  rw [part, card_image_of_injective _ (select_injective e s), card_univ, Fintype.card_fin]

omit [Fintype V] in
theorem mem_part (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) (i : Fin m) (b : Bool) :
    e (i,b) ∈ part e s ↔ b = s i := by
  simp only [part, mem_image, mem_univ, true_and, e.injective.eq_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨j, rfl, h⟩
    exact h.symm
  · intro h
    exact ⟨i, rfl, h.symm⟩

theorem compl_part (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) :
    (part e s)ᶜ = part e (fun i => !(s i)) := by
  ext v
  obtain ⟨⟨i,b⟩,rfl⟩ := e.surjective v
  simp only [mem_compl, mem_part]
  cases b <;> cases s i <;> decide

theorem card_compl_part (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) :
    (part e s)ᶜ.card = m := by rw [compl_part, card_part]

omit [Fintype V] in
theorem separates_pairs (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) (i : Fin m) :
    (e (i,true) ∈ part e s ↔ e (i,false) ∉ part e s) := by
  simp only [mem_part]
  cases s i <;> decide

omit [Fintype V] in
theorem sum_part (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) (f : V → ℝ) :
    (∑ v ∈ part e s, f v) = ∑ i, f (e (i,s i)) := by
  exact sum_image (fun i _ j _ h => select_injective e s h)

theorem difference_eq_signedSum (e : (Fin m × Bool) ≃ V) (s : Fin m → Bool) (f : V → ℝ) :
    (∑ v ∈ part e s, f v) - (∑ v ∈ (part e s)ᶜ, f v) =
      signedSum (fun i => f (e (i,true)) - f (e (i,false))) s := by
  rw [compl_part, sum_part, sum_part, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  cases s i <;> simp

/-- Balanced partition with an explicit finite size criterion, simultaneously
for all rows. All pairs of the given pairing are separated. -/
theorem exists_balanced_partition {R : Type*} [Fintype R]
    (e : (Fin m × Bool) ≃ V) (w : R → V → ℝ)
    (hw : ∀ r v, 0 ≤ w r v ∧ w r v ≤ 1) (b : ℝ) (hb : 0 ≤ b)
    (hsize : 15 * (Fintype.card R:ℝ) * (m:ℝ)^3 < b^6) :
    ∃ L : Finset V, L.card = m ∧ Lᶜ.card = m ∧
      (∀ i, (e (i,true) ∈ L ↔ e (i,false) ∉ L)) ∧
      ∀ r, |(∑ v ∈ L, w r v) - (∑ v ∈ Lᶜ, w r v)| < b := by
  let a : R → Fin m → ℝ := fun r i => w r (e (i,true)) - w r (e (i,false))
  have ha : ∀ r i, |a r i| ≤ 1 := by
    intro r i
    dsimp [a]
    rw [abs_le]
    obtain ⟨h0,h1⟩ := hw r (e (i,true))
    obtain ⟨h2,h3⟩ := hw r (e (i,false))
    constructor <;> linarith
  obtain ⟨s, hs⟩ := exists_signing_discrepancy m a ha b hb hsize
  refine ⟨part e s, card_part e s, card_compl_part e s, separates_pairs e s, ?_⟩
  intro r
  rw [difference_eq_signedSum]
  exact hs r

omit [DecidableEq V] in
/-- Complete any family of disjoint prescribed pairs to a pairing of V.
This is pure finite cardinality, independent of the matrix or graph. -/
theorem exists_pairing_extending (hcard : Fintype.card V = 2*m)
    {t : ℕ} (ht : t ≤ m) (p : (Fin t × Bool) ↪ V) :
    ∃ e : (Fin m × Bool) ≃ V, ∀ i b, e (Fin.castLE ht i,b) = p (i,b) := by
  let e₀ : (Fin m × Bool) ≃ V := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)
  let f : Fin t × Bool → V := fun z => e₀ (Fin.castLE ht z.1,z.2)
  have hf : Function.Injective f := by
    intro u v h
    have he := e₀.injective h
    apply Prod.ext
    · exact Fin.castLE_injective ht (congrArg Prod.fst he)
    · exact congrArg (fun z : Fin m × Bool => z.2) he
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f p hf p.injective
  exact ⟨e₀.trans σ, fun i b => hσ (i,b)⟩

/-- Fully quantified prescribed-pair version: the input supplies disjoint
pairs, not a balanced or degree-controlled partition. -/
theorem exists_balanced_partition_prescribed {R : Type*} [Fintype R]
    (hcard : Fintype.card V = 2*m) {t : ℕ} (ht : t ≤ m) (p : (Fin t × Bool) ↪ V)
    (w : R → V → ℝ) (hw : ∀ r v, 0 ≤ w r v ∧ w r v ≤ 1)
    (b : ℝ) (hb : 0 ≤ b) (hsize : 15 * (Fintype.card R:ℝ) * (m:ℝ)^3 < b^6) :
    ∃ L : Finset V, L.card = m ∧ Lᶜ.card = m ∧
      (∀ i, (p (i,true) ∈ L ↔ p (i,false) ∉ L)) ∧
      ∀ r, |(∑ v ∈ L, w r v) - (∑ v ∈ Lᶜ, w r v)| < b := by
  obtain ⟨e, he⟩ := exists_pairing_extending hcard ht p
  obtain ⟨L, hL, hC, hsep, hwL⟩ := exists_balanced_partition e w hw b hb hsize
  refine ⟨L, hL, hC, ?_, hwL⟩
  intro i
  simpa only [he] using hsep (Fin.castLE ht i)

end OverfullWork.PairedPartition
