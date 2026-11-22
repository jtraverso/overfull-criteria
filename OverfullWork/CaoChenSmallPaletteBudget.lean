module

public import OverfullWork.CaoChenPaletteLowLeafLinkage
public import OverfullWork.CaoChenLinkedPalettePacking

@[expose] public section


/-! # An actual small-root palette incidence budget

The sources and leaves below are finite sets of vertices of the given graph.
The budget is derived from the constructed palette links, properness, and
packing of common missing palettes, rather than supplied as a premise.
-/
namespace OverfullWork.CaoChenSmallPaletteBudget
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenDischarging CaoChenPaletteCounting CaoChenR1Continuation
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

noncomputable def lowSources (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (β : Fin G.maxDegree) : Finset V :=
  (neighboursS c q x y).filter fun u => β∈lowColours c q u

noncomputable def lowLeaves (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (β : Fin G.maxDegree) : Finset V :=
  univ.filter fun z => z≠x ∧ (G.degree z:ℝ)<q ∧
    ∃u∈neighboursS c q x y,c.col u z=some β

omit [DecidableEq V] in
private theorem spine_witness {c : PEC G (Fin G.maxDegree)} {q : ℝ} {x y u : V}
    (hu : u∈neighboursS c q x y) :
    ∃α,α∈paletteS c q x y ∧ c.col x u=some α := (mem_filter.mp hu).2

omit [DecidableEq V] in
private theorem spine_ne_endpoints {c : PEC G (Fin G.maxDegree)} {q : ℝ} {x y u : V}
    (hcm : IsColMinus c x y) (hu : u∈neighboursS c q x y) : u≠x ∧ u≠y := by
  obtain ⟨α,_,hxu⟩ := spine_witness hu
  refine ⟨(c.col_adj hxu).ne.symm,?_⟩
  intro he
  subst u
  rw [hcm.uncol] at hxu
  contradiction

omit [DecidableEq V] in
private theorem continuation_colour_ne {c : PEC G (Fin G.maxDegree)} {x u z : V}
    {α β : Fin G.maxDegree} (hxu : c.col x u=some α) (huz : c.col u z=some β)
    (hzx : z≠x) : β≠α := by
  intro he
  subst β
  have hux : c.col u x=some α := by rw [c.col_symm];exact hxu
  exact hzx (c.col_proper huz hux)

/-- A low continuation at an S-spine cannot have a root-missing colour.
A forced link would leave an isolated vertex of its one-colour graph. -/
theorem lowColours_subset_root_present (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (q : ℝ) (hq : 0<q) (hroom : (G.degree x:ℝ)+q+2≤(G.maxDegree:ℝ))
    {u : V} (hu : u∈neighboursS c q x y) :
    lowColours c q u⊆presentColours c x := by
  intro β hβ
  apply (mem_presentColours c x β).mpr
  intro hβx
  obtain ⟨z,huz,hzlow⟩ := (mem_lowColours c q u β).mp hβ
  obtain ⟨α,hαS,hxu⟩ := spine_witness hu
  have hzx : z≠x := by
    intro he
    subst z
    exact hβx u (by rw [c.col_symm];exact huz)
  have hβα := continuation_colour_ne hxu huz hzx
  have hβy : β∈presentColours c y :=
    (mem_presentColours c y β).mpr (fun hy => (hcm.ab_facts hcrit.2.1).1 β hβx hy)
  have hr := low_leaf_linked_of_palette_spine_present_right hcrit hcm hxu hβα huz
    q hq hroom hαS hβy hzlow hβx
  have hNbr : (c.kempeGraph β β).neighborSet x=∅ := by
    ext v
    simp only [mem_neighborSet,kempeGraph_adj,Set.mem_empty_iff_false,iff_false]
    rintro ⟨_,h|h⟩ <;> exact hβx v h
  exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hzx.symm hNbr hr

/-- Every edge at an S-spine is coloured, so its low-edge palette counts
exactly its graph neighbours below q. -/
theorem lowColours_card_eq_lowCount {c : PEC G (Fin G.maxDegree)} {x y : V}
    (hcm : IsColMinus c x y) (q : ℝ) (hx : (G.degree x:ℝ)<q)
    {u : V} (hu : u∈neighboursS c q x y) :
    (lowColours c q u).card=lowCount G q u := by
  obtain ⟨hux,huy⟩ := spine_ne_endpoints hcm hu
  have hpart := congrArg Finset.card (low_high_partition c q u)
  rw [card_union_of_disjoint (low_high_disjoint c q u),
    highColours_card_eq_highCount hcm q hx hux] at hpart
  have hp := CommonMissingColour.present_colour_card G.maxDegree c u
  change (presentColours c u).card=(colNbrs c u).card at hp
  have hc := hcm.card_colNbrs u
  simp only [hux,huy,or_self,if_false,add_zero] at hc
  have hl := lowCount_add_highCount G q u
  omega

/-- For a colour present at y, properness injects the sources into its
linked low leaves, with at most one extra source returning to x. -/
theorem present_right_source_card_le (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε)
    (hq : 0<(1-ε)*(G.maxDegree:ℝ))
    (hx : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2)
    (hroom : (G.degree x:ℝ)+(1-ε)*(G.maxDegree:ℝ)+2≤(G.maxDegree:ℝ))
    (K : ℕ) (hK : 2≤ε*(K:ℝ)) (β : Fin G.maxDegree)
    (hβy : β∈presentColours c y) :
    (lowSources c ((1-ε)*(G.maxDegree:ℝ)) x y β).card≤K+1 := by
  let q := (1-ε)*(G.maxDegree:ℝ)
  let T := lowLeaves c q x y β
  have hxT : x∉T := by simp [T,lowLeaves]
  have hlow : ∀z∈T,(G.degree z:ℝ)<q := by
    intro z hz
    exact (mem_filter.mp hz).2.2.1
  have hlink : ∀z∈T,∀κ,c.IsFree x κ → (c.kempeGraph κ β).Reachable x z := by
    intro z hz κ hκ
    obtain ⟨hzx,hzlow,u,hu,huz⟩ := (mem_filter.mp hz).2
    obtain ⟨α,hαS,hxu⟩ := spine_witness hu
    exact low_leaf_linked_of_palette_spine_present_right hcrit hcm hxu
      (continuation_colour_ne hxu huz hzx) huz q hq hroom hαS hβy hzlow hκ
  have hcap := CaoChenLinkedPalettePacking.epsilon_mul_card_lt_two_of_linked_low_leaves
    hcm β T ε hε hx hxT hlow hlink
  have hTK : T.card≤K := by
    have hh : (T.card:ℝ)<(K:ℝ) := by nlinarith only [hcap,hK,hε]
    exact Nat.le_of_lt (by exact_mod_cast hh)
  let A := lowSources c q x y β
  have hex : ∀u:V,∃z,u∈A → c.col u z=some β ∧ (G.degree z:ℝ)<q := by
    intro u
    by_cases hu : u∈A
    · obtain ⟨z,hcol,hz⟩ := (mem_lowColours c q u β).mp (mem_filter.mp hu).2
      exact ⟨z,fun _ => ⟨hcol,hz⟩⟩
    · exact ⟨x,fun hh => False.elim (hu hh)⟩
  choose f hf using hex
  have hmem : ∀u∈A,f u∈insert x T := by
    intro u hu
    by_cases he : f u=x
    · simp [he]
    · apply mem_insert_of_mem
      exact mem_filter.mpr ⟨mem_univ _,he,(hf u hu).2,u,(mem_filter.mp hu).1,(hf u hu).1⟩
  have hinj : Set.InjOn f (A:Set V) := by
    intro u hu v hv he
    have hu' : c.col (f u) u=some β := by rw [c.col_symm];exact (hf u hu).1
    have hv' : c.col (f u) v=some β := by rw [he,c.col_symm];exact (hf v hv).1
    exact c.col_proper hu' hv'
  have hcard := card_le_card_of_injOn f hmem hinj
  have hi := card_insert_le x T
  change A.card≤K+1
  omega

/-- The colours missing at y cost at most one root-degree budget.
For nonmaximum y they can occur only on their diagonal root edge;
for maximum y there is only one such colour. -/
theorem missing_right_source_sum_le_degree (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (q : ℝ) (hq : 0<q) (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ)) :
    (∑β∈presentColours c x\presentColours c y,(lowSources c q x y β).card)≤G.degree x := by
  let P := presentColours c x\presentColours c y
  have hNS : (neighboursS c q x y).card≤G.degree x :=
    (card_le_card (filter_subset _ _)).trans_eq (card_neighborFinset_eq_degree G x)
  by_cases hy : G.degree y<G.maxDegree
  · have hbound : ∀β∈P,(lowSources c q x y β).card≤1 := by
      intro β hβ
      have hnoty : β∉presentColours c y := (mem_sdiff.mp hβ).2
      have hfree : c.IsFree y β := by
        by_contra hn
        exact hnoty ((mem_presentColours c y β).mpr hn)
      have hrow : ∀u∈lowSources c q x y β,c.col x u=some β := by
        intro u hu
        obtain ⟨huNS,hβlow⟩ := mem_filter.mp hu
        obtain ⟨α,hαS,hxu⟩ := spine_witness huNS
        have hβα : β=α := by
          by_contra hne
          have hbad : β∈badColours c q u := mem_union.mpr (Or.inr hβlow)
          have hB := badColours_spine_subset_paletteB_of_paletteS_nonmaximum hcrit
            hcm hxu q hq hsmall hαS (Or.inl hy)
            (mem_sdiff.mpr ⟨hbad,by simpa only [mem_singleton] using hne⟩)
          obtain ⟨_,z,hyz,_⟩ := (mem_paletteB c q x y β).mp hB
          exact hfree z hyz
        rwa [hβα]
      apply card_le_one.mpr
      intro u hu v hv
      exact c.col_proper (hrow u hu) (hrow v hv)
    have hs := sum_le_sum hbound
    rw [sum_const,Nat.nsmul_eq_mul,mul_one] at hs
    have hP : P.card≤(presentColours c x).card := card_le_card sdiff_subset
    have hpres : (presentColours c x).card≤G.degree x := by
      have hp := CommonMissingColour.present_colour_card G.maxDegree c x
      have hc := hcm.card_colNbrs x
      simp only [true_or,if_true] at hc
      change (presentColours c x).card=(colNbrs c x).card at hp
      omega
    exact hs.trans (hP.trans hpres)
  · have hyD : G.degree y=G.maxDegree := le_antisymm (G.degree_le_maxDegree y) (by omega)
    have hm := hcm.card_missing_end (Or.inr rfl : y=x ∨ y=y)
    have hmissing : (missing c y).card=1 := by omega
    have hPsub : P⊆missing c y := by
      intro β hβ
      have hnoty := (mem_sdiff.mp hβ).2
      apply mem_missing.mpr
      by_contra hn
      exact hnoty ((mem_presentColours c y β).mpr hn)
    have hP : P.card≤1 := (card_le_card hPsub).trans_eq hmissing
    have hs : (∑β∈P,(lowSources c q x y β).card)≤P.card*(neighboursS c q x y).card := by
      calc
        _≤∑_β∈P,(neighboursS c q x y).card := sum_le_sum
          (fun β _ => card_le_card (filter_subset _ _))
        _=_ := by rw [sum_const,Nat.nsmul_eq_mul]
    change (∑β∈P,(lowSources c q x y β).card)≤_
    exact hs.trans ((Nat.mul_le_mul_right _ hP).trans (by simpa using hNS))

/-- Exact double counting of low edges from the actual S-spine set.
The palette links prove that only colours present at x contribute. -/
theorem sum_lowCount_eq_sum_sources (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (q : ℝ) (hq : 0<q) (hxlow : (G.degree x:ℝ)<q)
    (hroom : (G.degree x:ℝ)+q+2≤(G.maxDegree:ℝ)) :
    (∑u∈neighboursS c q x y,lowCount G q u)=
      ∑β∈presentColours c x,(lowSources c q x y β).card := by
  let A := neighboursS c q x y
  let P := presentColours c x
  let r : V → Fin G.maxDegree → Prop := fun u β => β∈lowColours c q u
  have hdouble := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s:=A) (t:=P) (r:=r)
  have hrow : ∀u∈A,(bipartiteAbove r P u).card=lowCount G q u := by
    intro u hu
    have heq : bipartiteAbove r P u=lowColours c q u := by
      ext β
      simp only [mem_bipartiteAbove,r]
      exact ⟨fun h => h.2,fun h => ⟨lowColours_subset_root_present hcrit hcm q hq hroom hu h,h⟩⟩
    rw [heq]
    exact lowColours_card_eq_lowCount hcm q hxlow hu
  have hcol : ∀β∈P,(bipartiteBelow r A β).card=(lowSources c q x y β).card := by
    intro β _
    rfl
  rw [sum_congr rfl hrow,sum_congr rfl hcol] at hdouble
  exact hdouble

/-- The concrete small-root budget. All threshold and cardinal assumptions
refer to graph degrees and an integer reciprocal of epsilon. -/
theorem sum_lowCount_neighboursS_le (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε)
    (hq : 0<(1-ε)*(G.maxDegree:ℝ))
    (hxlow : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hx : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2) (hd : 2≤G.degree x)
    (K : ℕ) (hK : 2≤ε*(K:ℝ)) :
    (∑u∈neighboursS c ((1-ε)*(G.maxDegree:ℝ)) x y,
      lowCount G ((1-ε)*(G.maxDegree:ℝ)) u)≤(K+2)*G.degree x := by
  let q := (1-ε)*(G.maxDegree:ℝ)
  have hdR : (2:ℝ)≤(G.degree x:ℝ) := by exact_mod_cast hd
  have hroom : (G.degree x:ℝ)+q+2≤(G.maxDegree:ℝ) := by dsimp [q];nlinarith only [hx,hdR]
  have hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ) := by linarith
  let P := presentColours c x
  let Q := presentColours c y
  let f := fun β => (lowSources c q x y β).card
  have hgood : (∑β∈P∩Q,f β)≤(K+1)*G.degree x := by
    have hs : (∑β∈P∩Q,f β)≤(P∩Q).card*(K+1) := by
      calc
        _≤∑_β∈P∩Q,(K+1) := sum_le_sum (fun β hβ => present_right_source_card_le
          hcrit hcm ε hε hq hx hroom K hK β (mem_inter.mp hβ).2)
        _=_ := by rw [sum_const,Nat.nsmul_eq_mul]
    have hp : P.card≤G.degree x := by
      have hh := CommonMissingColour.present_colour_card G.maxDegree c x
      have hc := hcm.card_colNbrs x
      simp only [true_or,if_true] at hc
      change P.card=(colNbrs c x).card at hh
      omega
    have hi : (P∩Q).card≤G.degree x := (card_le_card inter_subset_left).trans hp
    exact hs.trans (by nlinarith only [hi])
  have hbad : (∑β∈P\Q,f β)≤G.degree x := missing_right_source_sum_le_degree
    hcrit hcm q hq hsmall
  have hsplit : (∑β∈P,f β)=(∑β∈P∩Q,f β)+(∑β∈P\Q,f β) := by
    have hdis : Disjoint (P∩Q) (P\Q) := Finset.disjoint_left.mpr
      (fun β hβ hβ' => (mem_sdiff.mp hβ').2 (mem_inter.mp hβ).2)
    rw [←sum_union hdis]
    congr 1
    ext β
    simp only [mem_union,mem_inter,mem_sdiff]
    tauto
  have heq := sum_lowCount_eq_sum_sources hcrit hcm q hq hxlow hroom
  change (∑u∈neighboursS c q x y,lowCount G q u)≤_
  rw [heq]
  change (∑β∈P,f β)≤_
  rw [hsplit]
  nlinarith only [hgood,hbad]

end OverfullWork.CaoChenSmallPaletteBudget
