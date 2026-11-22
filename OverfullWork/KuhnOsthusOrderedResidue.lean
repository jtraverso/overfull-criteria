module

public import OverfullWork.KuhnOsthusResidueSpacing
public import OverfullWork.KuhnOsthusPreprocessingAssembly

@[expose] public section


/-! Kühn–Osthus Lemma 8.7. Decompose the ordinary 1-factor into
bounded matchings and order them for the chord-absorbing step. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

/-- A partition of the arcs of a digraph into cyclically spaced
matchings, with their assigned coarse interval pairs. -/
structure OrderedResidueMatchings (H : Digraph V) {g : ℕ} [NeZero g]
    (interval : V → Fin g) (q count capacity spacing : ℕ) where
  matching : Fin q → Digraph V
  doubleType : Fin q → ResidueDoubleType g
  matching_le : ∀ j, matching j ≤ H
  partition : ∀ x y, H.Adj x y ↔ ∃! j, (matching j).Adj x y
  pathSystem : ∀ j, IsDirectedPathSystem (matching j)
  noConsecutiveArcs : ∀ j x y z, (matching j).Adj x y → ¬ (matching j).Adj y z
  small : ∀ j, Fintype.card (Arc (matching j)) ≤ capacity
  endpoints : ∀ j x y, (matching j).Adj x y →
    interval x ∈ (doubleType j).val ∧ interval y ∈ (doubleType j).val
  typeCount : ∀ T, ((univ : Finset (Fin q)).filter (fun j => doubleType j = T)).card = count
  separated : ∀ i j, residueCyclicClose spacing i j →
    Disjoint (residueTypeClosure (doubleType i)) (residueTypeClosure (doubleType j))

/-- A vertex used by one matching cannot be used by another matching
within the prescribed cyclic distance. -/
theorem OrderedResidueMatchings.vertex_disjoint {H : Digraph V} {g q c m h : ℕ} [NeZero g]
    {interval : V → Fin g} (P : OrderedResidueMatchings H interval q c m h)
    {i j : Fin q} (hc : residueCyclicClose h i j) {x y u v : V}
    (he : (P.matching i).Adj x y) (hf : (P.matching j).Adj u v) :
    Disjoint ({x,y} : Finset V) {u,v} := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have endpoints {k : Fin q} {a b : V} (ha : (P.matching k).Adj a b) (hz : z ∈ ({a,b} : Finset V)) :
      interval z ∈ residueTypeClosure (P.doubleType k) := by
    apply subset_residue_type_closure
    obtain rfl | rfl := mem_insert.mp hz |>.imp_right mem_singleton.mp
    · exact (P.endpoints _ _ _ ha).1
    · exact (P.endpoints _ _ _ ha).2
  exact Finset.disjoint_left.mp (P.separated i j hc) (endpoints he hz) (endpoints hf hz')

/-- The cyclic partition with an arbitrary bin capacity. The repeated
ordering realizes each double-type exactly three times per bin. -/
theorem exists_ordered_residue_matchings (H : Digraph V)
    (hReg : ∀ v, inDegree H v = 1 ∧ outDegree H v = 1)
    (hLoop : ∀ v, ¬ H.Adj v v) {g : ℕ} [NeZero g] (interval : V → Fin g)
    (b m h : ℕ) (hg : 2 ≤ g) (hb : 0 < b) (hSize : Fintype.card V ≤ b*m)
    (hBig : 2*(2*h)*(10*g)+2*h+1 < g.choose 2) :
    Nonempty (OrderedResidueMatchings H interval (b*3*g.choose 2) (b*3) m h) := by
  obtain ⟨F,hF,_⟩ := exists_permutation_factorization_of_regular H 1 hReg
  let σ := F 0
  have hσ (x y : V) : H.Adj x y ↔ σ x = y := by
    rw [← hF]
    constructor
    · rintro ⟨i,hi⟩
      rw [Subsingleton.elim i (0 : Fin 1)] at hi
      exact hi
    · intro he
      exact ⟨0,he⟩
  obtain ⟨tag,hType,hCard,hColor⟩ := exists_residue_matching_labels σ
    (fun v he => hLoop v ((hσ v v).mpr he)) g b m hg hb hSize interval
  obtain ⟨order,hOrder⟩ := exists_residue_double_type_ordering g h hBig
  let n := g.choose 2
  let q := b*3*n
  let : NeZero n := ⟨by omega⟩
  let round : Fin q ≃ Fin (b*3) × Fin n := finProdFinEquiv.symm
  let toLabel : Fin (b*3) × Fin n ≃ Fin b × Fin 3 × ResidueDoubleType g :=
    ((finProdFinEquiv.symm.prodCongr order).trans (Equiv.prodAssoc _ _ _))
  let labels : Fin q ≃ Fin b × Fin 3 × ResidueDoubleType g := round.trans toLabel
  let D (j : Fin q) : Digraph V := ⟨fun x y => tag x = labels j ∧ σ x = y⟩
  let type (j : Fin q) : ResidueDoubleType g := order ((round j).2)
  have hLabel (i : Fin q) : (labels i).2.2 = type i := rfl
  have hRound (i : Fin q) : (round i).2 = (residueRoundIndex i : Fin n) := rfl
  have hMatch (i : Fin q) := residue_matching_of_label σ tag hColor (labels i)
  refine ⟨⟨D,type,(fun _ x y h => (hσ x y).mpr h.2),?_,fun i => (hMatch i).1,fun i => (hMatch i).2,?_,?_,?_,?_⟩⟩
  · intro x y
    rw [hσ]
    constructor
    · intro he
      refine ⟨labels.symm (tag x),⟨(labels.apply_symm_apply _).symm,he⟩,?_⟩
      intro i hi
      exact labels.injective (hi.1.symm.trans (labels.apply_symm_apply _).symm)
    · rintro ⟨i,hi,_⟩
      exact hi.2
  · intro i
    rw [← card_univ]
    refine (card_le_card_of_injOn (fun e : Arc (D i) => e.val.1) ?_ ?_).trans (hCard (labels i))
    · intro e _
      exact mem_filter.mpr ⟨mem_univ _,e.prop.1⟩
    · intro e _ f _ he
      apply Subtype.ext
      exact Prod.ext he (e.prop.2.symm.trans ((congrArg σ he).trans f.prop.2))
  · intro i x y he
    have hxy := hType x
    rw [he.1,he.2,hLabel] at hxy
    exact hxy
  · intro T
    let J := (univ : Finset (Fin q)).filter (fun j => type j = T)
    have hJ : J.card = (univ : Finset (Fin (b*3))).card := by
      apply card_bij (fun j _ => (round j).1)
      · intro _ _
        exact mem_univ _
      · intro i hi j hj he
        apply round.injective
        refine Prod.ext he (order.injective ?_)
        exact ((mem_filter.mp hi).2).trans ((mem_filter.mp hj).2).symm
      · intro a _
        let j := round.symm (a,order.symm T)
        have hr := round.apply_symm_apply (a,order.symm T)
        refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,congrArg Prod.fst hr⟩
        change order (round j).2 = T
        rw [hr,order.apply_symm_apply]
    simpa only [card_univ,Fintype.card_fin] using hJ
  · intro i j hi
    change Disjoint (residueTypeClosure (order (round i).2)) (residueTypeClosure (order (round j).2))
    rw [hRound,hRound]
    have hLen : h < n := by
      have hNonneg : 2*h ≤ 2*(2*h)*(10*g)+2*h+1 := by omega
      omega
    exact hOrder _ _ (residueCyclicClose_roundIndex (dvd_mul_left n (b*3)) hLen hi)

/-- An explicit admissible number of coarse intervals for spacing ten. -/
theorem residue_spacing_ten_bound {g : ℕ} (hg : 802 ≤ g) :
    400*g+21 < g.choose 2 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hg
  clear hg
  induction t with
  | zero => norm_num [Nat.choose_two_right]
  | succ t ih =>
    change 400*(802+t+1)+21 < (802+t+1).choose 2
    rw [Nat.choose_succ_succ' (802+t) 1, Nat.choose_one_right]
    change 400*(802+t+1)+21 < (802+t)+(802+t).choose 2
    omega

/-- Kühn–Osthus Lemma 8.7 with an explicit sufficient condition for
ordering the types and with room for integer rounding of the bins.
The paper takes the ordinary order to be the product of cluster count
and cluster size. -/
theorem kuhn_osthus_lemma_8_7 (H : Digraph V)
    (hReg : ∀ v, inDegree H v = 1 ∧ outDegree H v = 1)
    (hLoop : ∀ v, ¬ H.Adj v v) {g : ℕ} [NeZero g] (interval : V → Fin g)
    (b : ℕ) (hb : 0 < b) (hN : 3*b ≤ Fintype.card V)
    (hBig : 400*g+21 < g.choose 2) :
    let q := b*3*g.choose 2
    Nonempty (OrderedResidueMatchings H interval q (b*3) (2*g^2*Fintype.card V/q) 10) := by
  intro q
  let N := Fintype.card V
  let m := N/b+1
  have hg : 2 ≤ g := by
    by_contra! ht
    rw [Nat.choose_eq_zero_of_lt ht] at hBig
    omega
  have hq : 0 < q := by
    exact Nat.mul_pos (Nat.mul_pos hb (by decide)) (by omega)
  have hDiv := Nat.mod_add_div N b
  have hMod := Nat.mod_lt N hb
  have hLower : N ≤ b*m := by
    simp only [m,Nat.mul_add,Nat.mul_one]
    omega
  have hUpper : b*m ≤ N+b := by
    simp only [m,Nat.mul_add,Nat.mul_one]
    omega
  have hC : 2*g.choose 2 ≤ g^2 := by
    rw [Nat.choose_two_right, pow_two]
    have h := Nat.mul_le_mul_left g (Nat.sub_le g 1)
    omega
  have hBound : m ≤ 2*g^2*N/q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    calc
      m*q = (3*(b*m))*g.choose 2 := by simp only [q]; ac_rfl
      _ ≤ (4*N)*g.choose 2 := Nat.mul_le_mul_right _ (by omega)
      _ = (2*g.choose 2)*(2*N) := by ring
      _ ≤ 2*g^2*N := by simpa only [mul_assoc,mul_left_comm,mul_comm] using
        Nat.mul_le_mul_right (2*N) hC
  exact exists_ordered_residue_matchings H hReg hLoop interval b _ 10 hg hb
    (hLower.trans (Nat.mul_le_mul_left _ hBound))
    (by convert hBig using 1; ring_nf)

end OverfullWork.DirectedRobustExpansion
