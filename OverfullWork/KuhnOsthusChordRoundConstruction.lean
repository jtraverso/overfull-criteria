module

public import OverfullWork.KuhnOsthusChordOriginalSystems
public import OverfullWork.KuhnOsthusChordRoundScales

@[expose] public section


/-! Produce the balanced basic systems of one chord round from an
ordered factor, its paired exceptional systems, and a physical
universal-walk bank. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {W I : Type*} [Fintype W] [Fintype I]

/-- Two different slots of a batch of ten are within the cyclic
distance used in Lemmas 8.7 and 9.6. -/
theorem chord_batch_slots_close {b : ℕ} (a : Fin b) (i j : Fin 10) (h : i ≠ j) :
    residueCyclicClose 10
      (finProdFinEquiv (a,i) : Fin (b*10))
      (finProdFinEquiv (a,j)) := by
  let e : Fin b × Fin 10 ≃ Fin (b*10) := finProdFinEquiv
  have step (i j : Fin 10) (hlt : i.val < j.val) :
      ∃ d : Fin 10, ((e (a,i)).val+(d.val+1))%(b*10) = (e (a,j)).val := by
    let d : Fin 10 := ⟨j.val-i.val-1,by have := j.isLt; omega⟩
    have he : (e (a,i)).val+(d.val+1) = (e (a,j)).val := by
      change i.val+10*a.val+((j.val-i.val-1)+1) = j.val+10*a.val
      omega
    refine ⟨d,?_⟩
    rw [he,Nat.mod_eq_of_lt (e (a,j)).isLt]
  refine ⟨fun he => h (congrArg Prod.snd (e.injective he)),?_⟩
  rcases lt_or_gt_of_ne (fun he : i.val = j.val => h (Fin.ext he)) with he | he
  · obtain ⟨d,hd⟩ := step i j he
    exact ⟨d,Or.inl hd⟩
  · obtain ⟨d,hd⟩ := step j i he
    exact ⟨d,Or.inr hd⟩

/-- The balance and the per-cluster footprint for one whole round.
The assignment of exceptional systems is supplied in the order
guaranteed by Lemma 9.6. -/
theorem prepare_basic_chord_round {n b g count cap scale ell k m : ℕ} [NeZero g]
    (rank : W → Fin (n+2)) (quarter : W → Fin 4) (parent : Fin (n+2) → I)
    (s : Equiv.Perm I) (root : I) (σ : Equiv.Perm W)
    (H : Digraph W) (kind : W → Fin g)
    (P : OrderedResidueMatchings H kind (b*10) count cap 10)
    (C : Fin (b*10) → Digraph W) (owner : Fin (n+2) → I)
    (Q : Fin (n+2) × Fin 4 → Finset W)
    (M : ∀ j : Fin (n+2) × Fin 4, Fin k → Q j ≃ Q (finRotate (n+2) j.1,j.2))
    (hCycle : ∀ i, s.SameCycle root i) (hσ : ∀ x y, H.Adj x y ↔ σ x = y)
    (hM : 0 < k*m) (hQ : 110 < 10*b) (hScale : 24 ≤ scale)
    (hRoom : 3*(130*scale) ≤ m) (hSize : ∀ j, (Q j).card = m)
    (hCell : ∀ j v, v ∈ Q j → rank v = j.1 ∧ quarter v = j.2)
    (hBank : ∀ j p q, p ≠ q → ∀ x, M j p x ≠ M j q x)
    (hLo : (b*10)*(12*scale) ≤ 4*(k*m)) (hHi : 4*(k*m) ≤ (b*10)*(12*(scale+1)))
    (hFibre : ∀ x, (finiteSatisfying (fun j => parent j = x)).card = ell)
    (hCluster : ∀ x, (finiteSatisfying (fun v => parent (rank v) = x)).card =
      (finiteSatisfying (fun v => parent (rank v) = s x)).card)
    (hBlock : ∀ j x,
      (∑ e, if owner e = j ∧ parent e = x then (1:ℕ) else 0) + (if j = x then 1 else 0) =
      (∑ e, if owner e = j ∧ parent (finRotate (n+2) e) = s x then (1:ℕ) else 0) +
        (if j = s x then 1 else 0))
    (hCap : 3*cap ≤ scale)
    (hCPath : ∀ i, IsDirectedPathSystem (C i))
    (hCApart : ∀ i, Disjoint (finiteSatisfying (IncidentTo (P.matching i)))
      (finiteSatisfying (IncidentTo (C i))))
    (hSep : ∀ i j, residueCyclicClose 10 i j →
      Disjoint (finiteSatisfying (IncidentTo (P.matching i ⊔ C i)))
        (finiteSatisfying (IncidentTo (P.matching j ⊔ C j))))
    (hTouchC : ∀ i x, (finiteSatisfying (fun v => parent (rank v) = x ∧ IncidentTo (C i) v)).card ≤ cap)
    (hBalanceC : ∀ i x, (∑ e : Arc (C i), if parent (rank e.val.1) = x then (1:ℕ) else 0) =
      ∑ e : Arc (C i), if parent (rank e.val.2) = s x then (1:ℕ) else 0) :
    let e : Fin b × Fin 10 ≃ Fin (b*10) := finProdFinEquiv
    let next := finRotate (n+2)
    let U := successorCellMatchingUnion Q (next.prodCongr (Equiv.refl (Fin 4))) M
    let c := parent ∘ rank
    ∃ D : Fin b × Fin 10 → Digraph W,
      (∀ x y, U.Adj x y ↔ ∃! p, (D p).Adj x y) ∧ (∀ p, D p ≤ U) ∧
      (∀ p x, IncidentTo (D p) x → ¬ IncidentTo (P.matching (e p) ⊔ C (e p)) x) ∧
      ∀ p, let J := D p ⊔ (P.matching (e p) ⊔ C (e p))
        IsDirectedPathSystem J ∧
        (∀ x, (freeOut J c x).card = (freeIn J c (s x)).card) ∧
        ∀ x, (finiteSatisfying (fun v => c v = x ∧ IncidentTo J v)).card ≤
          scale+2*(ell*(13*scale)) := by
  intro e next U c
  obtain ⟨tag,hTag⟩ := P.exists_source_labels σ hσ
  have hF (x : I) :
      ((univ : Finset W).filter (fun v => c v = x)) = finiteSatisfying (fun v => c v = x) := by
    ext v
    simp
  have hCl (x : I) :
      ((univ : Finset W).filter (fun v => c v = x)).card =
        ((univ : Finset W).filter (fun v => c v = s x)).card := by
    rw [hF,hF]
    exact hCluster x
  obtain ⟨w,hw,hTotal,hBalance⟩ := exists_balanced_matching_chord_loads s root σ c
    P.matching tag parent (parent ∘ next) owner hCycle hCl hTag
    (fun i => (P.small i).trans (by omega)) hBlock hScale hLo hHi
  have hWidth : 3*scale*(10*b) ≤ k*m := by
    have hh : 4*(3*scale*(10*b)) ≤ 4*(k*m) := by
      convert hLo using 1
      ring
    omega
  have hTogether (i : Fin (b*10)) (v : W)
      (hv : IncidentTo (P.matching i) v) : ¬ IncidentTo (C i) v :=
    fun he => disjoint_left.mp (hCApart i) (mem_finiteSatisfying.mpr hv) (mem_finiteSatisfying.mpr he)
  have hTouch (i : Fin (b*10)) (x : I) :
      (finiteSatisfying (fun v => c v = x ∧ IncidentTo (P.matching i ⊔ C i) v)).card ≤ scale := by
    have hArc (g : Arc (P.matching i) → W) :
        (∑ a, if c (g a) = x then (1:ℕ) else 0) ≤ cap := by
      apply (sum_le_sum (fun a _ => show (if c (g a) = x then (1:ℕ) else 0) ≤ 1 by
        split <;> omega)).trans
      simpa only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] using P.small i
    have hH := (chord_footprint_le_endpoint_counts (P.matching i) (fun v => c v = x)).trans
      (Nat.add_le_add (hArc (fun a => a.val.1)) (hArc (fun a => a.val.2)))
    rw [chord_footprint_sup]
    exact (card_union_le _ _).trans ((Nat.add_le_add hH (hTouchC i x)).trans (by omega))
  have hLoads (j : Fin (n+2)) : (∑ a : Fin b,∑ i : Fin 10, w (e (a,i)) j) = 4*(k*m) := by
    exact (Fintype.sum_prod_type (fun p : Fin b × Fin 10 => w (e p) j)).symm.trans
      ((Equiv.sum_comp e (fun i => w i j)).trans (hTotal j))
  exact kuhn_osthus_chord_round_of_matching_loads scale ell rank quarter parent s
    (fun p => P.matching (e p)) (fun p => C (e p)) Q M (fun j p => w (e p) j)
    hM hQ hWidth hRoom hSize hCell hBank (fun j p => (hw (e p) j).1) (fun j p => (hw (e p) j).2)
    hLoads hFibre hCluster
    (fun p => (P.pathSystem (e p)).sup_of_disjoint_vertices (hCPath (e p)) (hTogether (e p)))
    (fun p x y hh hc => hTogether (e p) x (Or.inl ⟨y,hh⟩) (Or.inl ⟨y,hc⟩))
    (fun a i j hij => hSep _ _ (chord_batch_slots_close a i j hij))
    (fun p => hTouch (e p)) (fun p => hBalance (e p)) (fun p => hBalanceC (e p))

end OverfullWork.DirectedRobustExpansion
