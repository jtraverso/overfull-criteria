module

public import OverfullWork.ExceptionalMatchingPacking

@[expose] public section


/-! Split the arcs induced by the exceptional set into directed matchings.
The schedule uses endpoint sums and the direction of each arc, so
opposite arcs are scheduled separately. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
theorem exists_exceptional_matching_schedule (D : Digraph V) (S : Finset V)
    (hLoop : ∀ v ∈ S, ¬D.Adj v v) :
    ∃ M : Fin (4*S.card) → DirectedMatching V,
      (∀ j, (M j).size ≤ S.card) ∧
      (∀ j, (M j).toDigraph ≤ D) ∧
      (∀ i j, i ≠ j → ∀ v w, ¬((M i).toDigraph.Adj v w ∧ (M j).toDigraph.Adj v w)) ∧
      ∀ v ∈ S, ∀ w ∈ S, D.Adj v w → ∃ j, (M j).toDigraph.Adj v w := by
  let m := S.card
  let f := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let A := {e : (↑S) × (↑S) // D.Adj e.1.val e.2.val}
  let src (e : A) : Fin m := f e.val.1
  let dst (e : A) : Fin m := f e.val.2
  have hNe (e : A) : src e ≠ dst e := by
    intro h
    have he : e.val.1.val = e.val.2.val := congrArg Subtype.val (f.injective h)
    have hD := e.prop
    rw [←he] at hD
    exact hLoop _ e.val.1.prop hD
  let bit (e : A) := if (src e).val < (dst e).val then 0 else 1
  have hb (e : A) : bit e ≤ 1 := by dsimp [bit]; split_ifs <;> omega
  let color (e : A) : Fin (4*m) :=
    ⟨2*((src e).val+(dst e).val)+bit e,by
      have h₁ := (src e).isLt
      have h₂ := (dst e).isLt
      have hh := hb e
      omega⟩
  have hSame {e g : A} (h : color e = color g) :
      (src e).val+(dst e).val = (src g).val+(dst g).val ∧ bit e = bit g := by
    have he := congrArg Fin.val h
    dsimp only [color] at he
    have h₁ := hb e
    have h₂ := hb g
    omega
  have hSrc {e g : A} (hc : color e = color g) (h : e.val.1.val = g.val.1.val) : e = g := by
    have he : src e = src g := congrArg f (Subtype.ext h)
    have hv := (hSame hc).1
    rw [he] at hv
    have he' : dst e = dst g := Fin.ext (by omega)
    exact Subtype.ext (Prod.ext (f.injective he) (f.injective he'))
  have hDst {e g : A} (hc : color e = color g) (h : e.val.2.val = g.val.2.val) : e = g := by
    have he : dst e = dst g := congrArg f (Subtype.ext h)
    have hv := (hSame hc).1
    rw [he] at hv
    have he' : src e = src g := Fin.ext (by omega)
    exact Subtype.ext (Prod.ext (f.injective he') (f.injective he))
  have hSep {e g : A} (hc : color e = color g) : e.val.2.val ≠ g.val.1.val := by
    intro h
    have he : dst e = src g := congrArg f (Subtype.ext h)
    have hv := (hSame hc).1
    rw [←he] at hv
    have he' : (src e).val = (dst g).val := by omega
    have hne : (src e).val ≠ (dst e).val := fun h => hNe e (Fin.ext h)
    have hb' := (hSame hc).2
    dsimp only [bit] at hb'
    rw [←he,←he'] at hb'
    split_ifs at hb' <;> omega
  let C (j : Fin (4*m)) := {e : A // color e = j}
  let ix (j : Fin (4*m)) : Fin (Fintype.card (C j)) ≃ C j := (Fintype.equivFin (C j)).symm
  let M (j : Fin (4*m)) : DirectedMatching V :=
    { size := Fintype.card (C j)
      target := fun i => (ix j i).val.val.2.val
      source := fun i => (ix j i).val.val.1.val
      target_inj := fun i l h => (ix j).injective (Subtype.ext (hDst
        ((ix j i).prop.trans (ix j l).prop.symm) h))
      source_inj := fun i l h => (ix j).injective (Subtype.ext (hSrc
        ((ix j i).prop.trans (ix j l).prop.symm) h))
      separate := fun i l => hSep ((ix j i).prop.trans (ix j l).prop.symm) }
  have hClass (j : Fin (4*m)) (v w : V) :
      (M j).toDigraph.Adj v w ↔ ∃ e : A, color e = j ∧ e.val.1.val = v ∧ e.val.2.val = w := by
    constructor
    · rintro ⟨i,hv,hw⟩
      exact ⟨(ix j i).val,(ix j i).prop,hv,hw⟩
    · rintro ⟨e,hc,hv,hw⟩
      obtain ⟨i,hi⟩ := (ix j).surjective ⟨e,hc⟩
      exact ⟨i, (congrArg (fun z : C j => z.val.val.1.val) hi).trans hv,
        (congrArg (fun z : C j => z.val.val.2.val) hi).trans hw⟩
  refine ⟨M,?_,?_,?_,?_⟩
  · intro j
    have h := Fintype.card_le_of_injective (fun e : C j => e.val.val.1)
      (fun e g h => Subtype.ext (hSrc (e.prop.trans g.prop.symm) (congrArg Subtype.val h)))
    simpa only [Fintype.card_coe] using h
  · intro j v w h
    obtain ⟨e,_,rfl,rfl⟩ := (hClass j v w).mp h
    exact e.prop
  · intro i j hij v w h
    obtain ⟨e,he,ev,ew⟩ := (hClass i v w).mp h.1
    obtain ⟨g,hg,gv,gw⟩ := (hClass j v w).mp h.2
    have heg : e = g := Subtype.ext (Prod.ext (Subtype.ext (ev.trans gv.symm))
      (Subtype.ext (ew.trans gw.symm)))
    exact hij (he.symm.trans (heg ▸ hg))
  · intro v hv w hw h
    let e : A := ⟨(⟨v,hv⟩,⟨w,hw⟩),h⟩
    exact ⟨color e,(hClass _ _ _).mpr ⟨e,rfl,rfl,rfl⟩⟩

/-- A version of Kühn–Osthus Lemma 11.1 for a small exceptional set,
using at most four cycles per exceptional vertex. -/
theorem exists_hamilton_pack_covering_exceptional_set (ν τ α : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hντ : ν ≤ τ) (hτα : 128*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (D : Digraph W) (S : Finset W),
      N ≤ Fintype.card W →
      IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (outDegree D v:ℝ)) →
      8*(S.card:ℝ) ≤ ν*(Fintype.card W:ℝ)/2 →
      (S.card:ℝ) ≤ (ν/2)^4*(Fintype.card W:ℝ) →
      (∀ v ∈ S, ¬D.Adj v v) →
      ∃ σ : Fin (4*S.card) → Equiv.Perm W,
        (∀ j v,D.Adj v (σ j v)) ∧ (∀ j,HasSpanningCycle (fun x y => σ j x = y)) ∧
        (∀ i j, i ≠ j → ∀ v, σ i v ≠ σ j v) ∧
        ∀ v ∈ S, ∀ w ∈ S, D.Adj v w → ∃ j, σ j v = w := by
  obtain ⟨N,hN⟩ := exists_hamilton_pack_covering_matchings.{u} ν τ α hν hν1 hντ hτα hα
  refine ⟨N,?_⟩
  intro W _ D S hn hRob hIn hOut hBudget hSize hLoop
  obtain ⟨M,hM,hLe,hDis,hCover⟩ := exists_exceptional_matching_schedule D S hLoop
  have hK : 2*((4*S.card:ℕ):ℝ) ≤ ν*(Fintype.card W:ℝ)/2 := by push_cast; linarith only [hBudget]
  obtain ⟨σ,hσ,hC,hApart,hUse⟩ := hN D M hn hRob hIn hOut hK
    (fun j => (show ((M j).size:ℝ) ≤ S.card by exact_mod_cast hM j).trans hSize) hLe hDis
  refine ⟨σ,hσ,hC,hApart,?_⟩
  intro v hv w hw h
  obtain ⟨j,i,rfl,rfl⟩ := hCover v hv w hw h
  exact ⟨j,hUse j i⟩

end OverfullWork.DirectedRobustExpansion
