module

public import OverfullWork.KuhnOsthusPhysicalWalkOrdering
public import OverfullWork.DirectedDemandHall

@[expose] public section


/-! Realize the walk slots of Kühn–Osthus Lemma 9.5 as physical arcs.
The only possible directed circuit in one realization would use the
cut, whose two pairs use disjoint quarters. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Exact, acyclic arc partitions from the simultaneous orderings of
the fine successor pairs. The rank and quarter maps give the physical
coordinates. The last pair alone uses the half-turn in quarter order. -/
theorem exists_walk_arc_realization {n b m : ℕ} (s : ℕ)
    (rank : V → Fin (n+2)) (quarter : V → Fin 4)
    (source target : Fin (n+2) → Fin (4*m) → V)
    (w : Fin (n+2) → Fin b → Fin 10 → ℕ) (P : Fin b → Fin 10 → Finset V)
    (hM : 0 < m) (hQ : 110 < 10*b) (hWidth : 3*s*(10*b) ≤ m)
    (hSource : ∀ j p, rank (source j p) = j)
    (hTarget : ∀ j p, rank (target j p) = finRotate (n+2) j)
    (hSrcQuarter : ∀ j p, (quarter (source j p)).val =
      (p.val/m + if j = Fin.last (n+1) then 2 else 0)%4)
    (hDstQuarter : ∀ j p, (quarter (target j p)).val =
      (p.val/m + if j = Fin.last (n+1) then 2 else 0)%4)
    (hUnique : ∀ j, Function.Injective (fun p => (source j p,target j p)))
    (hWindow : ∀ j p q, p.val < q.val → q.val < p.val+130*s →
      source j p ≠ source j q ∧ target j p ≠ target j q)
    (hLo : ∀ j a i, 11*s ≤ w j a i) (hHi : ∀ j a i, w j a i ≤ 13*s)
    (hTotal : ∀ j, (∑ a,∑ i, w j a i) = 4*m)
    (hDis : ∀ a i i', i ≠ i' → Disjoint (P a i) (P a i'))
    (hMeet : ∀ j a i,
      (P a i ∩ finiteSatisfying (fun x => rank x = j)).card +
        (P a i ∩ finiteSatisfying (fun x => rank x = finRotate (n+2) j)).card ≤ 2*s) :
    let U : Digraph V := ⟨fun x y => ∃ j p, source j p = x ∧ target j p = y⟩
    ∃ D : Fin b × Fin 10 → Digraph V,
      (∀ x y, U.Adj x y ↔ ∃! p, (D p).Adj x y) ∧
      (∀ p, D p ≤ U) ∧
      (∀ p x y, (D p).Adj x y → rank y = finRotate (n+2) (rank x)) ∧
      (∀ a i, IsDirectedPathSystem (D (a,i))) ∧
      (∀ a i x, IncidentTo (D (a,i)) x → x ∉ P a i) ∧
      (∀ j a i, Fintype.card (Arc ⟨fun x y => (D (a,i)).Adj x y ∧ rank x = j⟩) = w j a i) := by
  intro U
  let load (j : Fin (n+2)) (a : Fin b) := ∑ i, w j a i
  let e (j : Fin (n+2)) : Fin (∑ a,load j a) ≃ Fin (4*m) := finCongr (hTotal j)
  have hReady (j : Fin (n+2)) :=
    exists_walk_pair_batch_partition (w j) P
      (finiteSatisfying (fun x => rank x = j))
      (finiteSatisfying (fun x => rank x = finRotate (n+2) j))
      s (130*s) (hLo j) (hHi j) le_rfl hDis (hMeet j)
      (source j ∘ e j) (target j ∘ e j)
      (fun p => mem_finiteSatisfying.mpr (hSource j (e j p)))
      (fun p => mem_finiteSatisfying.mpr (hTarget j (e j p)))
      (fun p q hp hq => hWindow j (e j p) (e j q) hp hq)
  choose piece place hPlace hInj hAvoid using hReady
  let pos (j : Fin (n+2)) (a : Fin b) (i : Fin 10) (p : Fin (w j a i)) :=
    e j (place j ⟨a,i,p⟩)
  let D (a : Fin b × Fin 10) : Digraph V :=
    ⟨fun x y => ∃ (j : Fin (n+2)) (p : Fin (w j a.1 a.2)),
      source j (pos j a.1 a.2 p) = x ∧ target j (pos j a.1 a.2 p) = y⟩
  have hPos (j : Fin (n+2)) (a : Fin b) (i : Fin 10) (p : Fin (w j a i)) :
      110*s*a.val ≤ (pos j a i p).val ∧ (pos j a i p).val < 130*s*(a.val+1) := by
    have hlo (a : Fin b) : 110*s ≤ load j a := by
      have h := sum_le_sum (s := (univ : Finset (Fin 10))) (fun i _ => hLo j a i)
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at h
      change 110*s ≤ ∑ i,w j a i
      nlinarith only [h]
    have hhi (a : Fin b) : load j a ≤ 130*s := by
      have h := sum_le_sum (s := (univ : Finset (Fin 10))) (fun i _ => hHi j a i)
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at h
      change (∑ i,w j a i) ≤ 130*s
      nlinarith only [h]
    change 110*s*a.val ≤ (place j ⟨a,i,p⟩).val ∧ (place j ⟨a,i,p⟩).val < 130*s*(a.val+1)
    rw [hPlace j a ⟨i,p⟩]
    exact walk_batch_position_bounds (load j) _ _ hlo hhi a (piece j a ⟨i,p⟩)
  have hStep (a : Fin b × Fin 10) (x y : V) (h : (D a).Adj x y) :
      rank y = finRotate (n+2) (rank x) := by
    obtain ⟨j,p,rfl,rfl⟩ := h
    rw [hSource,hTarget]
  have hSlot (j : Fin (n+2)) (a : Fin b) (i : Fin 10) :
      Function.Injective (fun p : Fin (w j a i) => source j (pos j a i p)) ∧
        Function.Injective (fun p : Fin (w j a i) => target j (pos j a i p)) := by
    have hP (p : Fin (w j a i)) :
        pos j a i p = e j (finSigmaFinEquiv ⟨a,piece j a ⟨i,p⟩⟩) := by
      exact congrArg (e j) (hPlace j a ⟨i,p⟩)
    constructor <;> intro p q hpq <;> dsimp only at hpq <;> rw [hP p,hP q] at hpq
    · exact (Sigma.mk.inj_iff.mp ((piece j a).injective ((hInj j a).1 hpq))).2.eq
    · exact (Sigma.mk.inj_iff.mp ((piece j a).injective ((hInj j a).2 hpq))).2.eq
  have hLe (p : Fin b × Fin 10) : D p ≤ U := by
    rintro x y ⟨j,q,hx,hy⟩
    exact ⟨j,_,hx,hy⟩
  refine ⟨D,?_,hLe,hStep,?_,?_,?_⟩
  · intro x y
    constructor
    · rintro ⟨j,q,hx,hy⟩
      obtain ⟨⟨a,i,p⟩,hp⟩ := ((place j).trans (e j)).surjective q
      have he : pos j a i p = q := hp
      refine ⟨(a,i),⟨j,p,he.symm ▸ hx,he.symm ▸ hy⟩,?_⟩
      rintro ⟨a',i'⟩ ⟨j',p',hx',hy'⟩
      have hj : j' = j := by rw [←hSource j' (pos j' a' i' p'),hx',←hx,hSource]
      subst j'
      have he' : pos j a' i' p' = q := hUnique j (Prod.ext (hx'.trans hx.symm) (hy'.trans hy.symm))
      have h := (place j).injective ((e j).injective (he'.trans he.symm))
      exact Prod.ext (congrArg Sigma.fst h) (congrArg (fun z => z.2.1) h)
    · rintro ⟨_,⟨j,p,hx,hy⟩,_⟩
      exact ⟨j,_,hx,hy⟩
  · intro a i
    apply walk_arcs_path_system_of_cut (D (a,i)) rank (hStep (a,i))
    · intro x hx y z hy hz
      obtain ⟨j,p,_,hp⟩ := hy
      obtain ⟨j',q,hq,_⟩ := hz
      have hj' : j' = 0 := by rw [←hSource j' (pos j' a i q),hq,hx]
      have hj : j = Fin.last (n+1) := (finRotate (n+2)).injective (by rw [←hTarget, hp,hx,finRotate_last])
      subst j'
      subst j
      let v := pos 0 a i q
      let v' := pos (Fin.last (n+1)) a i p
      have hWin := walk_batch_positions_in_short_window (10*b) s a.val v.val v'.val
        (Nat.mul_le_mul_left 10 a.isLt) hQ (hPos _ _ _ _).1 (hPos _ _ _ _).2
        (hPos _ _ _ _).1 (hPos _ _ _ _).2
      have hSep := walk_quarter_shift_separation m hM v v'
        (hWin.1.trans_le (Nat.add_le_add_left hWidth _))
        (hWin.2.trans_le (Nat.add_le_add_left hWidth _))
      have hZ : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by
        intro he
        have hV := congrArg Fin.val he
        simp at hV
      have hTogether : (quarter (source 0 v)).val = (quarter (target (Fin.last (n+1)) v')).val :=
        congrArg (fun t => (quarter t).val) (hq.trans hp.symm)
      rw [hSrcQuarter,hDstQuarter,if_neg hZ,if_pos rfl,Nat.add_zero,
        Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hM).mpr v.isLt)] at hTogether
      exact hSep hTogether
    · rintro x y z ⟨j,p,hx,hy⟩ ⟨j',q,hx',hz⟩
      have hj : j' = j := by rw [←hSource j' (pos j' a i q),hx',←hx,hSource]
      subst j'
      have hpq := (hSlot j a i).1 (hx.trans hx'.symm)
      exact hy.symm.trans ((congrArg (fun r => target j (pos j a i r)) hpq).trans hz)
    · rintro x y z ⟨j,p,hx,hz⟩ ⟨j',q,hy,hz'⟩
      have hj : j' = j := (finRotate (n+2)).injective (by rw [←hTarget j' (pos j' a i q),hz',←hz,hTarget])
      subst j'
      have hpq := (hSlot j a i).2 (hz.trans hz'.symm)
      exact hx.symm.trans ((congrArg (fun r => source j (pos j a i r)) hpq).trans hy)
  · intro a i x hx
    rcases hx with ⟨y,j,p,hx,_⟩ | ⟨y,j,p,_,hx⟩
    · exact hx ▸ (hAvoid j a i p).1
    · exact hx ▸ (hAvoid j a i p).2
  · intro j a i
    let R : Digraph V := ⟨fun x y => (D (a,i)).Adj x y ∧ rank x = j⟩
    let f (p : Fin (w j a i)) : Arc R :=
      ⟨(source j (pos j a i p),target j (pos j a i p)),
        ⟨⟨j,p,rfl,rfl⟩,hSource _ _⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro p q h
        exact (hSlot j a i).1 (congrArg (fun z : Arc R => z.val.1) h)
      · rintro ⟨⟨x,y⟩,⟨⟨j',p,hx,hy⟩,hRank⟩⟩
        have hj : j' = j := by rw [←hSource j' (pos j' a i p),hx,hRank]
        subst j'
        exact ⟨p,Subtype.ext (Prod.ext hx hy)⟩
    exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans (Fintype.card_fin _)

end OverfullWork.DirectedRobustExpansion
