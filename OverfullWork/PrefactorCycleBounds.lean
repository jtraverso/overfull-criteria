module

public import OverfullWork.PrefactorPathPreservation
public import Mathlib.Dynamics.PeriodicPts.Lemmas

@[expose] public section


/-! Orbit accounting after extending a prefactor, for Lo–Patel 5.3. -/
namespace OverfullWork.DirectedPrefactor
open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V] {D : Digraph V} {x : V}

noncomputable def orbit (σ : Equiv.Perm V) (v : V) : Finset V :=
  univ.filter (σ.SameCycle v)

theorem orbit_mem_iff (σ : Equiv.Perm V) (v w : V) :
    w∈orbit σ v ↔ σ.SameCycle v w := by simp [orbit]

theorem orbit_backward_mem (σ : Equiv.Perm V) (v : V) (i : ℕ) :
    (σ.symm : V → V)^[i] v∈orbit σ v := by
  apply (orbit_mem_iff σ v _).mpr
  apply Equiv.Perm.SameCycle.of_inv
  change Equiv.Perm.SameCycle (σ⁻¹) v (((σ⁻¹ : Equiv.Perm V) : V → V)^[i] v)
  have h : Equiv.Perm.SameCycle (σ⁻¹) v (((σ⁻¹)^i) v) :=
    Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  simpa only [Equiv.Perm.coe_pow] using h

theorem orbit_unchanged_of_avoids_origin_and_old_terminus (F : Prefactor D x)
    (z : V) (hz : z ≠ x) (ha : D.Adj (terminus F) z) (v : V)
    (hOrigin : x ∉ orbit (extend F z hz ha).successor v)
    (hEnd : terminus F ∉ orbit (extend F z hz ha).successor v) :
    orbit (extend F z hz ha).successor v = orbit F.successor v := by
  let G := extend F z hz ha
  change x ∉ orbit G.successor v at hOrigin
  change terminus F ∉ orbit G.successor v at hEnd
  have hZ : z ∉ orbit G.successor v := by
    intro hm
    have hc := (orbit_mem_iff G.successor v z).mp hm
    have hh : G.successor.SameCycle v (G.successor.symm z) :=
      Equiv.Perm.sameCycle_symm_apply_right.mpr hc
    rw [show G.successor.symm z=terminus F from predecessor_extend_at F z hz ha] at hh
    exact hEnd ((orbit_mem_iff _ _ _).mpr hh)
  have hIter : ∀ i : ℕ, (G.successor.symm : V → V)^[i] v =
      (F.successor.symm : V → V)^[i] v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply',iterate_succ_apply',←ih]
      have hm := orbit_backward_mem G.successor v i
      apply predecessor_extend_same F z hz ha
      · intro he
        rw [he] at hm
        exact hOrigin hm
      · intro he
        rw [he] at hm
        exact hZ hm
  have hMem : ∀ (σ : Equiv.Perm V) w,
      w ∈ orbit σ v ↔ ∃ i : ℕ,(σ.symm : V → V)^[i] v=w := by
    intro σ w
    constructor
    · intro hm
      obtain ⟨i,_,hi⟩ := ((orbit_mem_iff σ v w).mp hm).inv.exists_pow_eq'
      refine ⟨i,?_⟩
      change (((σ⁻¹ : Equiv.Perm V) : V → V)^[i]) v=w
      simpa only [Equiv.Perm.coe_pow] using hi
    · rintro ⟨i,rfl⟩
      exact orbit_backward_mem σ v i
  ext w
  change w ∈ orbit G.successor v ↔ w ∈ orbit F.successor v
  simp only [hMem,hIter]

/-- If the backward trace has k distinct vertices and the new end is
outside that trace, the new orbit containing the old end has ≥ k vertices.
The first k vertices of the backward trace suffice for both conditions. -/
theorem extend_old_terminus_orbit_card (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) (k : ℕ)
    (hLength : k ≤ minimalPeriod (F.successor.symm : V → V) (terminus F))
    (hAvoid : ∀ i < k,(F.successor.symm : V → V)^[i] (terminus F) ≠ F.successor.symm z) :
    k ≤ (orbit (extend F z hz ha).successor (terminus F)).card := by
  let v := terminus F
  let f : V → V := F.successor.symm
  let G := extend F z hz ha
  have hTrace := extend_preserves_backward_trace F z hz ha (k-1) ?_ ?_
  · let C := (range k).image (fun i => f^[i] v)
    have hCard : C.card=k := by
      rw [show C=(range k).image (fun i => f^[i] v) from rfl,card_image_iff.mpr ?_,card_range]
      intro i hi j hj he
      exact iterate_injOn_Iio_minimalPeriod
        ((mem_range.mp hi).trans_le hLength) ((mem_range.mp hj).trans_le hLength) he
    rw [←hCard]
    apply card_le_card
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    have hh := hTrace i (by have := mem_range.mp hi; omega)
    change ((G.successor.symm : V → V)^[i]) v=f^[i] v at hh
    rw [←hh]
    exact orbit_backward_mem G.successor v i
  · intro i hi he
    have his : i+1 < k := by omega
    have hn : f^[i+1] v=f^[0] v := by rw [iterate_succ_apply',he]; rfl
    have heq := iterate_injOn_Iio_minimalPeriod (his.trans_le hLength)
      ((show 0<k by omega).trans_le hLength) hn
    omega
  · intro i hi he
    have his : i+1 < k := by omega
    apply hAvoid (i+1) his
    rw [iterate_succ_apply',he]

/-- When the original short path ends inside the protected prefix,
the old terminus remains on the new open path. Every new closed orbit
then avoids the old terminus. -/
theorem old_terminus_stays_in_open_orbit (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) (k : ℕ)
    (hShort : ∃ i < k,(F.successor : V → V)^[i] x=terminus F)
    (hAvoid : ∀ i < k,(F.successor : V → V)^[i] x ≠ F.successor.symm z) :
    (extend F z hz ha).successor.SameCycle x (terminus F) := by
  classical
  let hEx : ∃ i : ℕ,(F.successor : V → V)^[i] x=terminus F :=
    ⟨hShort.choose,hShort.choose_spec.2⟩
  let m := Nat.find hEx
  have hm : m < k := (Nat.find_min' hEx hShort.choose_spec.2).trans_lt hShort.choose_spec.1
  have hOld : ∀ i < m,(F.successor : V → V)^[i] x ≠ terminus F :=
    fun _ hi => Nat.find_min hEx hi
  have he := extend_preserves_prefix F z hz ha m hOld
    (fun i hi => hAvoid i (hi.trans hm)) m le_rfl
  have hEnd := he.trans (Nat.find_spec hEx)
  have hc : (extend F z hz ha).successor.SameCycle x (((extend F z hz ha).successor^m) x) :=
    Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  simpa only [Equiv.Perm.coe_pow,hEnd] using hc

/-- Every non-origin orbit of size below k is an inherited orbit.
Either the path is short and protected in full at its beginning, or
the protected backward trace contains at least k distinct vertices. -/
theorem short_closed_orbit_inherited (F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) (k : ℕ)
    (hEither : (∃ i < k,(F.successor : V → V)^[i] x=terminus F) ∨
      k ≤ minimalPeriod (F.successor.symm : V → V) (terminus F))
    (hPrefix : ∀ i < k,(F.successor : V → V)^[i] x ≠ F.successor.symm z)
    (hSuffix : ∀ i < k,(F.successor.symm : V → V)^[i] (terminus F) ≠ F.successor.symm z)
    (v : V) (hOrigin : x ∉ orbit (extend F z hz ha).successor v)
    (hShort : (orbit (extend F z hz ha).successor v).card < k) :
    orbit (extend F z hz ha).successor v = orbit F.successor v := by
  let G := extend F z hz ha
  have hEnd : terminus F ∉ orbit G.successor v := by
    intro hh
    have hc := (orbit_mem_iff _ _ _).mp hh
    rcases hEither with h|h
    · have hxo := old_terminus_stays_in_open_orbit F z hz ha k h hPrefix
      exact hOrigin ((orbit_mem_iff _ _ _).mpr (hc.trans hxo.symm))
    · have he : orbit G.successor v=orbit G.successor (terminus F) := by
        ext w
        rw [orbit_mem_iff,orbit_mem_iff]
        exact ⟨fun hw => hc.symm.trans hw,fun hw => hc.trans hw⟩
      have hBound := extend_old_terminus_orbit_card F z hz ha k h hSuffix
      change (orbit G.successor v).card < k at hShort
      rw [he] at hShort
      exact (not_lt_of_ge hBound) hShort
  exact orbit_unchanged_of_avoids_origin_and_old_terminus F z hz ha v hOrigin hEnd

end OverfullWork.DirectedPrefactor
