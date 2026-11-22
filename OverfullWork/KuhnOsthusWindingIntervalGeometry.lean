module

public import OverfullWork.KuhnOsthusExceptionalEndpoints
public import OverfullWork.KuhnOsthusExceptionalRoutes

@[expose] public section


/-! Coordinates for the canonical intervals in Kühn–Osthus §7.4.
The half-open interval is a whole number of winding rounds, and
the omitted last cluster is the first cluster of the next interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The position in a fixed half-open interval of the global cycle. -/
def intervalPosition {p q : ℕ} (i : Fin p) : Fin q ↪ Fin (p*q) where
  toFun j := finProdFinEquiv (i,j)
  inj' _ _ h := congrArg Prod.snd (finProdFinEquiv.injective h)

@[simp]
theorem intervalPosition_val {p q : ℕ} (i : Fin p) (j : Fin q) :
    (intervalPosition i j).val = j.val+q*i.val := rfl

/-- The coarse cluster visited at a position of the wound cycle. -/
def windingParent {n : ℕ} (k : ℕ) (hk : 0 < k) (i : Fin n) : Fin k :=
  ⟨i.val % k,Nat.mod_lt _ hk⟩

theorem windingParent_intervalPosition {p b k : ℕ} (hk : 0 < k)
    (i : Fin p) (j : Fin (b*k)) :
    windingParent k hk (intervalPosition i j) = windingParent k hk j := by
  apply Fin.ext
  change (j.val+b*k*i.val)%k = j.val%k
  rw [show b*k*i.val = k*(b*i.val) by ring,Nat.add_mul_mod_self_left]

theorem finRotate_val_modulo {q : ℕ} (x : Fin q) :
    (finRotate q x).val = (x.val+1)%q := by
  cases q with
  | zero => exact x.elim0
  | succ q =>
    rw [coe_finRotate]
    by_cases h : x = Fin.last q
    · subst x
      simp
    · rw [if_neg h,Nat.mod_eq_of_lt]
      have hx := Fin.val_lt_last h
      omega

/-- In Hamilton cycle order, the winding relation of CSys7 forces
the parent labels to be the residues modulo the coarse cycle size. -/
theorem windingParent_of_successor_projection {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (parent : Fin n → Fin k)
    (hFirst : parent ⟨0,hn⟩ = ⟨0,hk⟩)
    (hNext : ∀ x, parent (finRotate n x) = finRotate k (parent x)) :
    ∀ x, parent x = windingParent k hk x := by
  have h : ∀ j (hj : j < n), (parent ⟨j,hj⟩).val = j%k := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h₀ : (parent ⟨0,hj⟩).val = 0 := congrArg Fin.val hFirst
      simpa only [Nat.zero_mod] using h₀
    | succ j ih =>
      intro hj
      let x : Fin n := ⟨j,Nat.lt_of_succ_lt hj⟩
      have hRot : finRotate n x = ⟨j+1,hj⟩ := by
        apply Fin.ext
        rw [finRotate_val_modulo,Nat.mod_eq_of_lt hj]
      have step := congrArg Fin.val (hNext x)
      rw [hRot,finRotate_val_modulo] at step
      have hx : (parent x).val = j%k := ih x.isLt
      rw [hx,Nat.mod_add_mod] at step
      exact step
  intro x
  apply Fin.ext
  exact h x.val x.isLt

/-- The global successor stays in the interval until its last
position, then goes to the first position of the next interval. -/
theorem intervalPosition_next {p q : ℕ} (hq : 0 < q) (i : Fin p) (j : Fin q) :
    finRotate (p*q) (intervalPosition i j) =
      if j.val+1=q then intervalPosition (finRotate p i) ⟨0,hq⟩
      else intervalPosition i (finRotate q j) := by
  apply Fin.ext
  by_cases h : j.val+1=q
  · rw [if_pos h,finRotate_val_modulo,intervalPosition_val,intervalPosition_val,
      finRotate_val_modulo]
    change (j.val+q*i.val+1)%(p*q) = 0+q*((i.val+1)%p)
    rw [show j.val+q*i.val+1 = q*(i.val+1) by
      calc
        _ = (j.val+1)+q*i.val := by ring
        _ = _ := by rw [h]; ring,
      mul_comm p q,Nat.mul_mod_mul_left,zero_add]
  · rw [if_neg h,finRotate_val_modulo,intervalPosition_val,intervalPosition_val,
      finRotate_val_modulo]
    have hj : j.val+1<q := by have := j.isLt; omega
    rw [Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt]
    · ring
    · have hStep : q*i.val+q ≤ p*q := by
        rw [←Nat.mul_succ,mul_comm p q]
        exact Nat.mul_le_mul_left q i.isLt
      omega

/-- The next interval differs from the present one when there are
at least two intervals on the cycle. -/
theorem finRotate_interval_ne_self {p : ℕ} (hp : 2 ≤ p) (i : Fin p) :
    finRotate p i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [finRotate_val_modulo] at hv
  by_cases hs : i.val+1<p
  · rw [Nat.mod_eq_of_lt hs] at hv
    omega
  · have hEnd : i.val+1=p := by have := i.isLt; omega
    rw [hEnd,Nat.mod_self] at hv
    omega

/-- Each coarse cluster has exactly one position per complete winding
round in the interval. -/
theorem windingParent_fibres (b k : ℕ) (hk : 0 < k) (u : Fin k) :
    fibreWeight (windingParent (n := b*k) k hk) univ u = b := by
  have hm : (univ : Finset (Fin b × Fin k)).map finProdFinEquiv.toEmbedding =
      (univ : Finset (Fin (b*k))) := univ_map_equiv_to_embedding _
  have hBase (x : Fin b × Fin k) : windingParent k hk (finProdFinEquiv x) = x.2 := by
    apply Fin.ext
    change (x.2.val+k*x.1.val)%k = x.2.val
    exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt x.2.isLt)
  unfold fibreWeight
  rw [←hm]
  exact card_winding_interval_fibre b _ _ hBase u

/-- The positions available for exceptional endpoints are away from
the identified boundary and both of its cyclic neighbours. -/
noncomputable def windingEndpointPositions {q : ℕ} (boundary : Fin q) : Finset (Fin q) :=
  univ \ {boundary,finRotate q boundary,(finRotate q).symm boundary}

theorem mem_windingEndpointPositions {q : ℕ} (boundary x : Fin q) :
    x ∈ windingEndpointPositions boundary ↔
      x ≠ boundary ∧ (finRotate q).symm x ≠ boundary ∧ finRotate q x ≠ boundary := by
  simp only [windingEndpointPositions,mem_sdiff,mem_univ,true_and,mem_insert,mem_singleton,not_or]
  let s := finRotate q
  change (x ≠ boundary ∧ x ≠ s boundary ∧ x ≠ s.symm boundary) ↔ _
  exact and_congr_right (fun _ => and_congr
    (not_congr (s.symm.eq_symm_apply))
    (not_congr s.eq_symm_apply))

/-- The safe interior drops three positions from the half-open
interval, hence retains at least `b-3` copies of every coarse cluster. -/
theorem winding_interior_copies (b k : ℕ) (hk : 0 < k) (boundary : Fin (b*k)) :
    ∀ u, b-3 ≤
      ((windingEndpointPositions boundary).filter (fun j => windingParent k hk j = u)).card := by
  intro u
  let F := (univ : Finset (Fin (b*k))).filter (fun j => windingParent k hk j = u)
  have hF : F.card = b := by
    have h := windingParent_fibres b k hk u
    unfold fibreWeight at h
    convert h using 2
    ext j
    simp [F]
  let B : Finset (Fin (b*k)) := {boundary,finRotate (b*k) boundary,(finRotate (b*k)).symm boundary}
  have hSub : F \ B ⊆ (windingEndpointPositions boundary).filter
      (fun j => windingParent k hk j = u) := by
    intro x hx
    obtain ⟨hf,hb⟩ := mem_sdiff.mp hx
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hb⟩,(mem_filter.mp hf).2⟩
  have hLost : B.card ≤ 3 := card_le_three
  have hCover := card_le_card_sdiff_add_card (s := F) (t := B)
  have hCount := card_le_card hSub
  omega

/-- CSys6 and the full rounds in a canonical interval give a uniform
blow-up of the coarse reduced digraph. This form gives the integer
robust expansion premise of the chord scheduler. -/
theorem winding_interval_integer_expansion {p b k : ℕ}
    (R₀ : Digraph (Fin k)) (R : Digraph (Fin (p*(b*k)))) (i : Fin p)
    (hb : 0 < b) (hk : 0 < k)
    (hLift : ∀ x y, R.Adj x y ↔ R₀.Adj (windingParent k hk x) (windingParent k hk y))
    (ν τ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hOrder : 2 ≤ τ*(k:ℝ)) (hR : IsRealRobust R₀ ν τ) :
    let Q : Digraph (Fin (b*k)) := ⟨fun x y => R.Adj (intervalPosition i x) (intervalPosition i y)⟩
    IsRobustAt Q ⌈(ν^2/2)*((b*k:ℕ):ℝ)⌉₊ ⌈(2*τ)*((b*k:ℕ):ℝ)⌉₊ ∧
      ∀ x, inDegree Q x = inDegree R₀ (windingParent k hk x)*b ∧
        outDegree Q x = outDegree R₀ (windingParent k hk x)*b := by
  classical
  dsimp only
  let f := windingParent (n := b*k) k hk
  have hQ : (⟨fun x y => R.Adj (intervalPosition i x) (intervalPosition i y)⟩ :
      Digraph (Fin (b*k))) = fibrePullback R₀ f f := by
    ext x y
    change R.Adj (intervalPosition i x) (intervalPosition i y) ↔ R₀.Adj (f x) (f y)
    rw [hLift,windingParent_intervalPosition hk i x,windingParent_intervalPosition hk i y]
  rw [hQ]
  have hFib := windingParent_fibres b k hk
  have hRob := fibrePullback_realRobust R₀ f f b hFib hFib hb ν τ hν hντ hτ
    (by simpa only [Fintype.card_fin] using hOrder) hR
  refine ⟨?_,fibrePullback_semidegrees R₀ f f b hFib hFib⟩
  have hν₀ : 0 ≤ ν^2/2 := by positivity
  simpa only [Fintype.card_fin] using integer_of_real _ _ _ hν₀ hRob

end OverfullWork.DirectedRobustExpansion
