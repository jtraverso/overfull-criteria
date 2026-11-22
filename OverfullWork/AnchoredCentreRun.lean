module

public import OverfullWork.AnchoredCentreStep

@[expose] public section


/-! # Finite second-anchor saturation with a paid neighbor reserve

The reserve is n+1 distinct available neighbors, where n colors are
missing at the second anchor. Each step consumes at most one neighbor
and one missing color. All colored copies at the first anchor survive.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 16000000

inductive AnchoredRun (A : Finset V) (a b : V) :
    M.PartialColouring k → M.PartialColouring k → ℕ → ℕ → Prop
  | refl (P) : AnchoredRun A a b P P 0 0
  | step {P Q R n t} (h : AnchoredStep P Q A a b) (tail : AnchoredRun A a b Q R n t) :
      AnchoredRun A a b P R (n+1) (h.step.removed.edgeCount+t)

theorem AnchoredRun.toCentreRun {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) : CentreRun b P Q n t := by
  induction h with
  | refl P => exact CentreRun.refl P
  | step h _ ih => exact CentreRun.step h.step ih

theorem AnchoredRun.anchor_bundle {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) (hab : a ≠ b) (v : V) :
    Q.graph.mult s(a,v)=P.graph.mult s(a,v) := by
  induction h with
  | refl P => rfl
  | step h _ ih => exact ih.trans (h.anchor_bundle hab v)

theorem AnchoredRun.anchor_degree {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) (hab : a ≠ b) :
    Q.graph.degree a=P.graph.degree a := by
  simp only [degree_eq_sum_mult]
  exact sum_congr rfl (fun v _ => h.anchor_bundle hab v)

theorem AnchoredRun.removed_bound {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) : t ≤ n := by
  induction h with
  | refl P => omega
  | step h _ ih => have hh := h.step.erased_le_one;omega

theorem AnchoredRun.second_bundle {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) (v : V) (hv : v ∉ A) :
    Q.graph.mult s(b,v)=P.graph.mult s(b,v) := by
  induction h with
  | refl P => rfl
  | step h _ ih => exact ih.trans (h.second_bundle v hv)

theorem AnchoredRun.away_bundle_le {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) (e : Sym2 V) (hb : b ∉ e) :
    Q.graph.mult e ≤ P.graph.mult e := by
  induction h with
  | refl P => exact le_refl _
  | step h _ ih => exact ih.trans (h.away_bundle_le e hb)

theorem AnchoredRun.edgeCount_mono {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) : P.graph.edgeCount ≤ Q.graph.edgeCount := by
  induction h with
  | refl P => exact le_refl _
  | step h _ ih => exact h.step.edgeCount_mono.trans ih

theorem AnchoredRun.free_loss_le {A : Finset V} {a b : V} {P Q : M.PartialColouring k} {n t : ℕ}
    (h : AnchoredRun A a b P Q n t) :
    (P.ordinaryFree A a b).card ≤ (Q.ordinaryFree A a b).card+n := by
  induction h with
  | refl P => omega
  | step h _ ih => have hh := h.free_loss_le;omega

theorem AnchoredRun.total_missing_mono {A : Finset V} {a b : V} {P Q : M.PartialColouring k}
    {n t : ℕ} (h : AnchoredRun A a b P Q n t) :
    (∑ v, (Q.colouring.missingPalette v).card) ≤ (∑ v, (P.colouring.missingPalette v).card) := by
  rw [←Q.colouring.sum_missing_card_eq,←P.colouring.sum_missing_card_eq]
  exact sum_le_sum (fun i _ => h.toCentreRun.missingSet_mono i)

theorem exists_anchored_saturated_run (A : Finset V) (a b : V) (hb : b ∉ A)
    (P : M.PartialColouring k)
    (hReserve : (P.colouring.missingPalette b).card+1 ≤ (P.ordinaryFree A a b).card) :
    ∃ Q t, AnchoredRun A a b P Q (P.colouring.missingPalette b).card t ∧
      t ≤ (P.colouring.missingPalette b).card ∧
      (∀ i, (Q.colouring.colourGraph i).degree b=1) := by
  suffices ∀ n : ℕ, ∀ P : M.PartialColouring k, (P.colouring.missingPalette b).card=n →
      n+1 ≤ (P.ordinaryFree A a b).card →
      ∃ Q t, AnchoredRun A a b P Q n t ∧ t ≤ n ∧
        (∀ i, (Q.colouring.colourGraph i).degree b=1) from this _ P rfl hReserve
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hCount hRoom
    by_cases hn : n=0
    · refine ⟨P,0,?_,by omega,?_⟩
      · rw [hn];exact AnchoredRun.refl P
      · intro i
        have hc := P.colouring.colourGraph_degree_le_one i b
        by_contra hne
        have hz : (P.colouring.colourGraph i).degree b=0 := by omega
        have hi : i ∈ P.colouring.missingPalette b := mem_filter.mpr ⟨mem_univ _,hz⟩
        have hh := card_pos.mpr ⟨i,hi⟩
        omega
    obtain ⟨Q,⟨hStep⟩⟩ := exists_anchored_step P A a b hb (by omega) (by omega)
    have hP := P.colouring.missingPalette_card_add_degree b
    have hQ := Q.colouring.missingPalette_card_add_degree b
    have hGain := hStep.step.centre_gain
    have hless : (Q.colouring.missingPalette b).card < n := by omega
    have hNext : (Q.colouring.missingPalette b).card+1 ≤ (Q.ordinaryFree A a b).card := by
      have hh := hStep.free_loss_le
      omega
    obtain ⟨R,t,hRun,ht,hSat⟩ := ih _ hless Q rfl hNext
    have hnEq : (Q.colouring.missingPalette b).card+1=n := by omega
    refine ⟨R,hStep.step.removed.edgeCount+t,?_,?_,hSat⟩
    · rw [←hnEq];exact AnchoredRun.step hStep hRun
    · have hh := hStep.step.erased_le_one;omega

theorem AnchoredRun.preserves_saturation {A : Finset V} {a b : V} {P Q : M.PartialColouring k}
    {n t : ℕ} (h : AnchoredRun A a b P Q n t) (hab : a ≠ b)
    (hSat : ∀ i, (P.colouring.colourGraph i).degree a=1) :
    ∀ i, (Q.colouring.colourGraph i).degree a=1 := by
  have hP : P.graph.degree a=k := by
    rw [←P.colouring.sum_colour_degree a]
    simp only [hSat,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  have hQ := h.anchor_degree hab
  have hMissing := Q.colouring.missingPalette_card_add_degree a
  intro i
  have hc := Q.colouring.colourGraph_degree_le_one i a
  by_contra hne
  have hz : (Q.colouring.colourGraph i).degree a=0 := by omega
  have hi : i ∈ Q.colouring.missingPalette a := mem_filter.mpr ⟨mem_univ _,hz⟩
  have hh := card_pos.mpr ⟨i,hi⟩
  omega

end SimpleGraph.MultiGraph.PartialColouring
