module

public import OverfullWork.KuhnOsthusWoundChordFactors
public import OverfullWork.KuhnOsthusIndexedChordBlocks
public import OverfullWork.KuhnOsthusCanonicalChordIntervals
public import OverfullWork.KuhnOsthusGlobalChordPreparation

@[expose] public section


/-! Prepare the rounds of Lemma 9.7 from the physical exceptional
factors and the ordered universal walk. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs DirectedDemandHall InducedDigraphSampling
open scoped Classical

set_option maxHeartbeats 900000 in
/-- The same interval partition, exceptional factors and walk bank
prepare every regular ordinary residue. The exact physical arc set
includes the residue, the bank, and the original exceptional factors. -/
theorem prepare_chord_systems_from_wound_factors {V : Type*} [Fintype V]
    {G : Digraph V} {r g u n p t ell w a m b d : ℕ}
    (Z : Finset V) (hg : 802 ≤ g) (hu : 0 < u) (ha : 0 < a) (hell : 0 < ell)
    (hm : m = 4*ell*a) (hLarge : 24*(g*u) ≤ 8*g^2*m) (hFine : 4*ell*390*(8*g^2) ≤ g*u)
    (hBC : b*10 = (g*u)*((g*u)*(n+1))) (hCount : b*10 = d*3*g.choose 2)
    (hd : 0 < d) (hSize : 3*d ≤ Fintype.card ↥Zᶜ) (hPC : p*t = (g*u)*(n+1))
    (hSlotsMin : 300 ≤ (g*u)*p) (hWalkSize : 2 ≤ w) :
    let f := g*u
    let k := f*(n+1)
    let s := finRotate k
    let bank := 96*ell*g^2*k
    let scale := (8*g^2*m)/f
    let K := scale+2*(ell*(13*scale))
    ∀ (c : ↥Zᶜ → Fin k) (order : Fin w ≃ Fin ell × Fin k)
      (l : Fin k → List (Fin k)) (W : Fin ell → Equiv.Perm (Fin k))
      (Q : Fin w × Fin 4 → Finset ↥Zᶜ)
      (M : ∀ j : Fin w × Fin 4, Fin (r*bank) → Q j ≃ Q (finRotate w j.1,j.2))
      (C : Fin p × Fin k → Finset V) (mStyle : ℕ) (_hTouch : mStyle*(g*u) ≤ 2*g^2*m),
    let parent (j : Fin w) := (order j).2
    let next := (Equiv.refl (Fin p)).prodCongr (finRotate f)
    let A (j : Fin p × Fin f) := univ.biUnion (fun i : Fin (n+1) => C (j.1,intervalPosition j.2 i))
    let S (j : Fin p × Fin f) := C (j.1,intervalPosition j.2 (0 : Fin (n+1)))
    ∀ (F : Fin (r*t) → ∀ j, OriginalInterval G Z (A j ∪ S (next j)) (S j) (S (next j))),
    (∀ j, (Q j).card = a) → (∀ j v, v ∈ Q j → c v = parent j.1) →
    (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) →
    (∀ j i i', i ≠ i' → ∀ x, M j i x ≠ M j i' x) →
    (∀ v, ∃ j, v ∈ Q j) →
    (∀ j, parent (finRotate w j) = W (order j).1 (parent j)) →
    (∀ j, (j :: l j).getLast? = some (s j)) →
    (∀ x y, ((univ : Finset (Fin ell)).filter (fun j => W j x = y)).card =
      elementaryChordMultiplicity s l x y + if s x = y then
        ell - (∑ z, elementaryChordMultiplicity s l x z) else 0) →
    (∀ j, (C j).card = mStyle) → (∀ j, Disjoint (C j) Z) → (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
    (∀ x ∉ Z, ∃ j, x ∈ C j) → (∀ j (v : ↥Zᶜ), v.val ∈ C j → c v = j.2) →
    Pairwise (fun i j => Disjoint (⨆ v, (F i v).digraph) (⨆ v, (F j v).digraph)) →
    let E : Digraph V := ⨆ i, ⨆ j, (F i j).digraph
    let U : Digraph ↥Zᶜ := successorCellMatchingUnion Q ((finRotate w).prodCongr (Equiv.refl (Fin 4))) M
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    ∀ H : Digraph V,
      (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) →
      (∀ x, inDegree (induced H Zᶜ) x = r ∧ outDegree (induced H Zᶜ) x = r) →
      (∀ x, ¬ H.Adj x x) →
      Disjoint H (liftDirectedPair e e U) → Disjoint (H ⊔ liftDirectedPair e e U) E →
      Nonempty (PreparedChordSystems (H ⊔ liftDirectedPair e e U ⊔ E)
        Z c s K (Fin r × Fin (f*k))) := by
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le hWalkSize
  have hw : w = z+2 := by omega
  clear hz
  subst w
  intro f k s bank scale K cluster order l W Q M C mStyle hTouch parent next A S F
    hQ hParent hQDis hM hCoverQ hStep hEnd hMult hC hCZ hDisC hCoverC hLabel hF E U e H hSupp hHReg hHLoop hHU hE
  let loc (v : ↥Zᶜ) := (hCoverQ v).choose
  let rank (v : ↥Zᶜ) := (loc v).1
  let quarter (v : ↥Zᶜ) := (loc v).2
  have hRank (j : Fin (z+2) × Fin 4) (v : ↥Zᶜ) (hv : v ∈ Q j) : rank v = j.1 ∧ quarter v = j.2 := by
    have hLoc : loc v = j := by
      by_contra hne
      exact disjoint_left.mp (hQDis _ _ hne) (hCoverQ v).choose_spec hv
    exact ⟨congrArg Prod.fst hLoc,congrArg Prod.snd hLoc⟩
  have hCoord : cluster = parent ∘ rank := funext (fun v => hParent (loc v) v (hCoverQ v).choose_spec)
  subst cluster
  let c := parent ∘ rank
  have hFPos : 0 < f := Nat.mul_pos (by omega) hu
  have hF₂ : 2 ≤ f := (show 2 ≤ g by omega).trans (Nat.le_mul_of_pos_right _ hu)
  have hKPos : 0 < k := Nat.mul_pos hFPos (by omega)
  have hK₂ : 2 ≤ k := hF₂.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hMPos : 0 < m := by rw [hm]; positivity
  have : NeZero g := ⟨by omega⟩
  change b*10 = f*k at hBC
  change p*t = k at hPC
  have hBPos : 0 < b*10 := hBC.symm ▸ Nat.mul_pos hFPos hKPos
  have : NeZero (b*10) := ⟨hBPos.ne'⟩
  let root : Fin k := ⟨0,hKPos⟩
  have hCycle (x : Fin k) : s.SameCycle root x :=
    (isCycle_finRotate_of_le hK₂).sameCycle (finRotate_interval_ne_self hK₂ _) (finRotate_interval_ne_self hK₂ _)
  obtain ⟨hFibre,walkOwner,hBlock⟩ := indexed_walk_chord_blocks s l root W order hStep hEnd (fun x y => by
    convert hMult x y using 1
    · congr 1
      exact filter_congr_decidable _ _ _
    · by_cases h : s x = y <;> simp [h])
  have hCluster (x : Fin k) : (finiteSatisfying (fun v => c v = x)).card = m :=
    (physical_walk_quarter_cluster_card rank quarter parent Q ell a hFibre hCoverQ hRank hQ x).trans hm.symm
  obtain ⟨hScale,hLo,hHi,_,hRoom,hCapB,_⟩ :=
    chord_round_integer_scales f g ell k m a hFPos hKPos hm hLarge hFine
  let split : Fin k ≃ Fin f × Fin (n+1) := finProdFinEquiv.symm
  let owner (j : Fin f) : Fin g := (finProdFinEquiv.symm j : Fin g × Fin u).1
  let coarse (v : ↥Zᶜ) := owner (split (c v)).1
  let area (j : Fin f) := finiteSatisfying (fun v => (split (c v)).1 = j)
  let cells (j : Fin f × Fin p) := (A (j.2,j.1)).subtype (· ∈ Zᶜ)
  let D (i : Fin r) (j : Fin f × (Fin p × Fin t)) := (F (finProdFinEquiv (i,j.2.2)) (j.2.1,j.1)).digraph
  have hArea (j : Fin f) (v : ↥Zᶜ) (hv : v ∈ area j) : coarse v = owner j :=
    congrArg owner ((mem_finiteSatisfying (p := fun z => (split (c z)).1 = j)).mp hv)
  have hOwnerSize (z : Fin g) : (finiteSatisfying (fun j => owner j = z)).card ≤ u :=
    ((canonical_chord_interval_labels g u (n+1)).2.2 z).le
  have hSub (j : Fin f × Fin p) : cells j ⊆ area j.1 := by
    intro v hv
    obtain ⟨z,_,hz⟩ := mem_biUnion.mp (mem_subtype.mp hv)
    exact mem_finiteSatisfying.mpr ((congrArg (fun k => (split k).1) (hLabel _ v hz)).trans
      (congrArg Prod.fst (split.apply_symm_apply (j.1,z))))
  have hSlotCard : Fintype.card (Fin f × (Fin p × Fin t)) = b*10 := by
    rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin,hPC,hBC]
  let slot : Fin (b*10) ≃ Fin f × (Fin p × Fin t) := (Fintype.equivFinOfCardEq hSlotCard).symm
  have hCoarse : 200*g ≤ g.choose 2 := by have h := residue_spacing_ten_bound hg; omega
  have hSlots : 200 ≤ b*10 := by
    rw [hCount]
    have h := Nat.le_mul_of_pos_left (g.choose 2) (show 0 < d*3 by positivity)
    omega
  have ht : 300*t ≤ b*10 := by
    rw [hBC,←hPC,←Nat.mul_assoc]
    exact Nat.mul_le_mul_right t hSlotsMin
  have hOrdSize : Fintype.card ↥Zᶜ = k*m := by
    classical
    let B (i : Fin k) := finiteSatisfying (fun v => c v = i)
    have hUnion : univ.biUnion B = univ := by
      ext v
      simp only [mem_biUnion,mem_univ,true_and,B,mem_finiteSatisfying,iff_true]
      exact ⟨c v,rfl⟩
    have hDis : (↑(univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint B := by
      intro i _ j _ hij
      exact disjoint_left.mpr (fun v hv hv' => hij (
        ((mem_finiteSatisfying (p := fun z => c z = i)).mp hv).symm.trans
        ((mem_finiteSatisfying (p := fun z => c z = j)).mp hv')))
    rw [←card_univ,←hUnion,card_biUnion hDis]
    simp only [B,hCluster,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]
  have hCap : 3*(2*g^2*Fintype.card ↥Zᶜ/(b*10)) ≤ scale := by rwa [hOrdSize,hBC]
  have hTouch' : mStyle ≤ 2*g^2*Fintype.card ↥Zᶜ/(b*10) := by
    apply (Nat.le_div_iff_mul_le hBPos).mpr
    rw [hBC,hOrdSize]
    calc
      mStyle*(f*k) = (mStyle*f)*k := (Nat.mul_assoc mStyle f k).symm
      _ ≤ (2*g^2*m)*k := Nat.mul_le_mul_right k hTouch
      _ = 2*g^2*(k*m) := by ring
  obtain ⟨hUnion,hDDis,hApart,hData⟩ := wound_chord_factor_round_data Z C c hF₂ hC hCZ hDisC hCoverC hLabel F hF
  change (⨆ i : Fin r × (Fin f × (Fin p × Fin t)), D i.1 i.2) = E at hUnion
  have hLift : liftDirectedPair e e (induced H Zᶜ) = H := by
    ext x y
    constructor
    · rintro ⟨a,b,rfl,rfl,h⟩
      exact h
    · intro h
      obtain ⟨hx,hy⟩ := hSupp x y h
      exact ⟨⟨x,mem_compl.mpr hx⟩,⟨y,mem_compl.mpr hy⟩,rfl,rfl,h⟩
  have hApartHU : Disjoint (induced H Zᶜ) U := by
    apply disjoint_iff_inf_le.mpr
    rintro x y ⟨hx,hy⟩
    exact disjoint_iff_inf_le.mp hHU ⟨hx,(liftDirectedPair_adj e e U x y).mpr hy⟩
  rw [←hUnion,←hLift] at hE ⊢
  have hPrepared := prepare_chord_systems_from_interval_cells Z rank quarter parent s root (induced H Zᶜ)
    coarse area owner (finRotate f) cells slot D walkOwner Q M hHReg (fun x => hHLoop x.val)
    hd hSize hg hCount hSlots hCoarse
    (Nat.mul_le_mul_right u (by omega)) ht hArea hOwnerSize hSub hApart hCycle (Nat.mul_pos (by positivity) ha)
    hScale hRoom hQ hRank hM (by rw [hBC]; exact hLo) (by rw [hBC]; exact hHi) hFibre
    (fun x => (hCluster x).trans (hCluster (s x)).symm) hBlock hCap
    (fun _ _ h => hDDis h) (fun i j => ⟨(hData i j).1,(hData i j).2.1⟩)
    (fun i j => (hData i j).2.2.1) hApartHU hE
    (fun i j v hv => by simpa only [mem_union] using (hData i j).2.2.2.1 hv)
    (fun i j x => ((hData i j).2.2.2.2.1 x).trans hTouch') (fun i j x => by
      convert (hData i j).2.2.2.2.2 x using 1 <;> apply sum_congr rfl <;> intro z _ <;> split_ifs <;> rfl)
  exact ⟨hPrepared.some.reindex (finProdFinEquiv.trans (finCongr (congrArg (r*·) hBC.symm)))⟩

end OverfullWork.DirectedRobustExpansion
