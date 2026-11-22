module

public import OverfullWork.DirectedPackingAllStages
public import OverfullWork.DirectedPackingUndirectedRemainder
public import OverfullWork.DirectedLayoutPadding

@[expose] public section


/-! The Gao--Shan orientation and reserve reduction for the spanning
configurations in CMS Lemma 3.14. Host edges and fixed copies have
separate labels, including when they have the same unordered endpoints. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage
open scoped Classical
universe u v w

/-- The copy-indexed CMS layout theorem for a simple host. Fixed edges
are arbitrary prescribed copies, so the configurations themselves
may be multigraphs. -/
theorem cms_lemma_3_14_indexed (a gap ν τ : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hgap : 0 < gap) (hgapA : gap ≤ a) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτgap : 16384*τ ≤ gap) :
    ∃ ε ν' : ℝ, 0 < ε ∧ 0 < ν' ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
        (G : SimpleGraph V) [DecidableRel G.Adj] (L : J → Layout V I) (long : J → I),
        let n := Fintype.card V
        N ≤ n → RobustExpansion.IsRealRobust G ν τ →
        (∀ v, |(G.degree v:ℝ)-a*(n:ℝ)| ≤ ε*(n:ℝ)) →
        (Fintype.card J:ℝ) ≤ ((a-gap)/2)*(n:ℝ) →
        (∀ i, ((L i).boundary.card:ℝ) ≤ ε*(n:ℝ) ∧ long i ∉ (L i).fixed ∧
          (((univ \ insert (long i) (L i).fixed).card:ℕ):ℝ) ≤ ε*(n:ℝ)) →
        (∀ v, ((∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v):ℕ):ℝ)
          ≤ ε*(n:ℝ)) →
        (∀ v, (visits (fun i => (L i).boundary) v:ℝ) ≤ ε*(n:ℝ)) →
        ∃ (O : Digraph V) (P : PackingPrefix O L (univ : Finset J)),
          IsOrientationOf O G ∧ RobustExpansion.IsRealRobust (G \ hostEdges G P.used) ν' τ ∧
          Pairwise (fun i j => Disjoint (unorderedCopy '' P.copiesAt i) (unorderedCopy '' P.copiesAt j)) ∧
          ∀ (i : (univ : Finset J)) j, j ∉ (L i.val).fixed →
            ((P.round i).word j).IsChain G.Adj ∧ ((P.round i).word j).Nodup := by
  let p := gap/(2*a)
  let γ := gap/4
  let δ := a/2-gap/4
  let νD := p*ν/24
  have hp : 0 < p := by dsimp [p]; positivity
  have hp₁ : p < 1 := (div_lt_iff₀ (by positivity : 0 < 2*a)).mpr (by linarith only [ha,hgapA])
  have hνD : 0 < νD := by dsimp [νD]; positivity
  have hτp := hν.trans_le hντ
  have hνDτ : νD ≤ τ := by
    have h := mul_le_mul_of_nonneg_right hp₁.le hν.le
    dsimp [νD]
    linarith only [h,hντ,hν]
  have hτ : τ ≤ 1/8 := by linarith only [hτgap,hgapA,ha₁]
  have hγα : γ/2 ≤ 1 := by dsimp [γ]; linarith only [hgapA,ha₁]
  have hγτ : 256*(8*τ) ≤ γ/2 := by dsimp [γ]; linarith only [hτgap]
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ₁ : γ ≤ 1 := by dsimp [γ]; linarith only [hgapA,ha₁]
  have hδ₁ : δ ≤ 1 := by dsimp [δ]; linarith only [ha₁,hgap]
  obtain ⟨t,ht,N₀,hPack⟩ := exists_directed_layout_packing.{u,v,w} νD τ (γ/2) γ (γ/2)
    hνD hνDτ hτ hγα hγτ hγ (by positivity)
  let ε := min (t/2) (a/8)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεT : 2*ε ≤ t := by
    have hh : ε ≤ t/2 := min_le_left _ _
    linarith only [hh]
  have hεA : 8*ε ≤ a := by
    have hh : ε ≤ a/8 := min_le_right _ _
    linarith only [hh]
  obtain ⟨N₁,hOrient⟩ := exists_centered_oriented_reserve.{u} a p ν τ ε ha hp hp₁ hν hτp.le hε hεA
  refine ⟨ε,2*νD,hε,by positivity,max N₀ N₁,?_⟩
  intro V _ I _ J _ G _ L long
  dsimp only
  intro hn hRob hDeg hm hLay hEnd hAp
  let n := Fintype.card V
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  obtain ⟨D,Γ,hOr,hDis,hD,hΓ,hR⟩ := hOrient G (by omega) hRob hDeg
  have hγEq : p*a/2 = γ := by dsimp [p,γ]; field_simp; ring
  have hδEq : (1-p)*a/2 = δ := calc
    _ = a/2-p*a/2 := by ring
    _ = δ := by rw [hγEq]
  have hR' : IsRealRobust Γ (3*νD) τ := by
    convert hR using 1
    dsimp only [νD]
    ring
  have hBound := mul_le_mul_of_nonneg_right hεT hnR
  have hD' : SemidegreesAround D (δ*(n:ℝ)) (t*(n:ℝ)) := by
    rw [← hδEq]
    exact fun v => ⟨(hD v).1.trans hBound,(hD v).2.trans hBound⟩
  have hΓ' : SemidegreesAround Γ (γ*(n:ℝ)) (t*(n:ℝ)) := by
    rw [← hγEq]
    exact fun v => ⟨(hΓ v).1.trans hBound,(hΓ v).2.trans hBound⟩
  have hmN : Fintype.card J ≤ n := by
    have hh := mul_le_mul_of_nonneg_right (show (a-gap)/2 ≤ 1 by linarith only [ha₁,hgap]) hnR
    have hd : (Fintype.card J:ℝ) ≤ (n:ℝ) := hm.trans (by simpa only [one_mul] using hh)
    exact_mod_cast hd
  have hGap : γ*(n:ℝ)+(Fintype.card J:ℝ) ≤ δ*(n:ℝ) := by
    dsimp only [γ,δ]
    linarith only [hm]
  have hInc : ε*(n:ℝ) ≤ t*(n:ℝ) := by
    have hh := mul_nonneg hε.le hnR
    linarith only [hh,hBound]
  obtain ⟨P,hRes⟩ := hPack δ γ hδ₁ (by ring_nf; rfl) hγ₁ D Γ L long
    (by omega) hmN hDis hR' hGap hD' hΓ'
    (fun i => ⟨(hLay i).1.trans hInc,(hLay i).2.1,(hLay i).2.2.trans hInc⟩)
    (fun v => (hEnd v).trans hInc) (fun v => (hAp v).trans hInc)
  exact ⟨D ⊔ Γ,P,hOr,robust_host_after_packing hOr le_sup_right P.used_le hRes,
    P.unordered_copies_pairwise hOr,fun i j hj => (P.round i).undirected_path hOr j hj⟩

/-- A disjoint realization of all prescribed layouts in a simple host,
with independent fixed copies. The used directed graph records just
the host arcs consumed in the undirected remainder. -/
structure CMSPacking {V J : Type*} (I : J → Type*) (G : SimpleGraph V)
    (L : ∀ j, Layout V (I j)) where
  orientation : Digraph V
  isOrientation : IsOrientationOf orientation G
  configuration : ∀ j, Realization orientation (L j)
  host_disjoint : Pairwise (fun i j => Disjoint (configuration i).used (configuration j).used)

def CMSPacking.used {V J : Type*} {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) : Digraph V :=
  ⨆ j, (P.configuration j).used

/-- The individual occurrence labels of a spanning configuration.
A host edge and a prescribed copy may have the same endpoints. -/
def CMSPacking.copies {V J : Type*} {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) (i : J) :
    Set (Sym2 V ⊕ (Σ j, I j)) :=
  {c | match c with
      | .inl e => e ∈ (hostEdges G (P.configuration i).used).edgeSet
      | .inr ⟨j,k⟩ => j = i ∧ k ∈ (L j).fixed}

theorem CMSPacking.copies_pairwise {V J : Type*} {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) :
    Pairwise fun i j => Disjoint (P.copies i) (P.copies j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro c hi hj
  cases c with
  | inr c =>
    have h₁ : c.1 = i := hi.1
    have h₂ : c.1 = j := hj.1
    exact hij (h₁.symm.trans h₂)
  | inl e =>
    induction e using Sym2.inductionOn with
    | hf x y =>
      change s(x,y) ∈ (hostEdges G (P.configuration i).used).edgeSet at hi
      change s(x,y) ∈ (hostEdges G (P.configuration j).used).edgeSet at hj
      rw [SimpleGraph.mem_edgeSet] at hi hj
      have forbid (u v : V) (h₁ : (P.configuration i).used.Adj u v)
          (h₂ : (P.configuration j).used.Adj u v) : False :=
        disjoint_iff_inf_le.mp (P.host_disjoint hij) (show
          ((P.configuration i).used ⊓ (P.configuration j).used).Adj u v from ⟨h₁,h₂⟩)
      rcases hi.2 with hi | hi <;> rcases hj.2 with hj | hj
      · exact forbid x y hi hj
      · exact P.isOrientation.2.2 x y ⟨(P.configuration i).used_le hi,(P.configuration j).used_le hj⟩
      · exact P.isOrientation.2.2 x y ⟨(P.configuration j).used_le hj,(P.configuration i).used_le hi⟩
      · exact forbid y x hi hj

theorem CMSPacking.flexible_path {V J : Type*} {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) (j : J) (i : I j)
    (hi : i ∉ (L j).fixed) :
    ((P.configuration j).word i).IsChain G.Adj ∧ ((P.configuration j).word i).Nodup :=
  (P.configuration j).undirected_path P.isOrientation i hi

theorem CMSPacking.fixed_path {V J : Type*} {I : J → Type*} {G : SimpleGraph V}
    {L : ∀ j, Layout V (I j)} (P : CMSPacking I G L) (j : J) (i : I j)
    (hi : i ∈ (L j).fixed) :
    (P.configuration j).word i = [(L j).source i,(L j).target i] := by
  simp only [Realization.word,(P.configuration j).fixed_empty i hi,List.cons_append,List.nil_append]

set_option maxHeartbeats 8000000 in
/-- CMS Lemma 3.14, with simple host, arbitrary finite layouts and fixed
edge occurrences, and an explicitly positive robust remainder. The
outputs are paths and their disjoint copy labels. The conclusion retains
the same interval parameter as the input robust expander. -/
theorem cms_lemma_3_14 (a gap ν τ : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hgap : 0 < gap) (hgapA : gap ≤ a) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτgap : 16384*τ ≤ gap) :
    ∃ ε ν' : ℝ, 0 < ε ∧ 0 < ν' ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] {J : Type w} [Fintype J]
        (I : J → Type v) [∀ j, Fintype (I j)]
        (G : SimpleGraph V) [DecidableRel G.Adj] (L : ∀ j, Layout V (I j)) (long : ∀ j, I j),
        let n := Fintype.card V
        N ≤ n → RobustExpansion.IsRealRobust G ν τ →
        (∀ v, |(G.degree v:ℝ)-a*(n:ℝ)| ≤ ε*(n:ℝ)) →
        (Fintype.card J:ℝ) ≤ ((a-gap)/2)*(n:ℝ) →
        (∀ i, ((L i).boundary.card:ℝ) ≤ ε^2*(n:ℝ) ∧ long i ∉ (L i).fixed ∧
          (Fintype.card (I i):ℝ) ≤ ε^4*(n:ℝ)) →
        (∀ v, ((∑ i, ((L i).endpointLoad true v+(L i).endpointLoad false v):ℕ):ℝ)
          ≤ ε^3*(n:ℝ)) →
        (∀ v, (visits (fun i => (L i).boundary) v:ℝ) ≤ ε^2*(n:ℝ)) →
        ∃ P : CMSPacking I G L, RobustExpansion.IsRealRobust (G \ hostEdges G P.used) ν' τ := by
  obtain ⟨t,ν',ht,hν',N,hPack⟩ := cms_lemma_3_14_indexed.{u,max v w,w}
    a gap ν τ ha ha₁ hgap hgapA hν hντ hτgap
  let ε := min t 1
  have hε : 0 < ε := lt_min ht (by norm_num)
  have hε₁ : ε ≤ 1 := min_le_right _ _
  have hεT : ε ≤ t := min_le_left _ _
  have hPow (k : ℕ) (hk : 0 < k) : ε^k ≤ t := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hε.le hε₁) hε.le).trans
      (by simpa using hεT)
  refine ⟨ε,ν',hε,hν',N,?_⟩
  intro V _ J _ I _ G _ L long
  dsimp only
  intro hn hR hDeg hm hLayout hEnd hAp
  let K := Σ j, I j
  letI : DecidableEq K := Classical.decEq _
  let f (j : J) : I j ↪ K := ⟨Sigma.mk j,fun x y he => eq_of_heq (Sigma.mk.inj he).2⟩
  let L' (j : J) : Layout V K := (L j).pad (long j) (f j)
  have hnR : 0 ≤ (Fintype.card V:ℝ) := Nat.cast_nonneg _
  have h₂ := mul_le_mul_of_nonneg_right (hPow 2 (by decide)) hnR
  have h₃ := mul_le_mul_of_nonneg_right (hPow 3 (by decide)) hnR
  have h₄ := mul_le_mul_of_nonneg_right (hPow 4 (by decide)) hnR
  let long' (j : J) := f j (long j)
  have hLay' (j : J) : ((L' j).boundary.card:ℝ) ≤ t*(Fintype.card V:ℝ) ∧
      long' j ∉ (L' j).fixed ∧
      ((univ \ insert (long' j) (L' j).fixed).card:ℝ) ≤ t*(Fintype.card V:ℝ) :=
    ⟨(hLayout j).1.trans h₂,fun h => (hLayout j).2.1 ((L j).mem_pad_fixed _ _ _ |>.mp h),
      (show (((univ \ insert (f j (long j)) (L' j).fixed).card:ℕ):ℝ) ≤ Fintype.card (I j) by
        exact_mod_cast (L j).pad_short_count_le (long j) (f j)).trans ((hLayout j).2.2.trans h₄)⟩
  obtain ⟨O,Q,hO,hRes,_,_⟩ := hPack (I := K) G L' long' hn hR
    (fun v => (hDeg v).trans (mul_le_mul_of_nonneg_right hεT hnR)) hm hLay'
    (fun v => by simpa only [L',Layout.pad_endpointLoad] using (hEnd v).trans h₃)
    (fun v => (hAp v).trans h₂)
  let P : CMSPacking I G L := {
    orientation := O
    isOrientation := hO
    configuration := fun j => Realization.unpad (long := long j) (f := f j) (Q.round ⟨j,mem_univ _⟩)
    host_disjoint := by
      intro i j hij
      change Disjoint (Q.round ⟨i,mem_univ _⟩).unpad.used (Q.round ⟨j,mem_univ _⟩).unpad.used
      rw [Realization.used_unpad,Realization.used_unpad]
      exact Q.disjoint (fun he => hij (congrArg Subtype.val he)) }
  have hUsed : P.used = Q.used := by
    ext x y
    simp only [CMSPacking.used,P,PackingPrefix.used,Digraph.iSup_adj,Realization.used_unpad]
    exact ⟨fun ⟨i,hi⟩ => ⟨⟨i,mem_univ _⟩,hi⟩,fun ⟨i,hi⟩ => ⟨i.val,hi⟩⟩
  let robust (U : Digraph V) := RobustExpansion.IsRealRobust (G \ hostEdges G U) ν' τ
  have hQ : robust Q.used := hRes
  rw [← hUsed] at hQ
  exact ⟨P,hQ⟩

end OverfullWork.DirectedSpanningConfiguration
