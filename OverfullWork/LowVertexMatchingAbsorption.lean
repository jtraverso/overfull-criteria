module

public import OverfullWork.DenseHall
public import OverfullWork.MaximumCoreTwoStructure
public import OneFactor.Extend

@[expose] public section


/-! # Two actual matchings saturating the low-degree vertices

This proves the matching step of Chen--McDonald--Shan Lemma 3.4 from
Vizing's adjacency lemma, including the degree-comparison Hall argument.
It does not claim that these matchings also saturate every maximum vertex,
or that deleting them preserves the absence of overfull subsets.
-/
namespace OverfullWork.LowVertexMatchingAbsorption
open SimpleGraph Finset Overfull
open scoped Classical
set_option maxHeartbeats 4000000

/-- The local degree comparison in a bipartite relation implies Hall's
condition. Fractional edge weights are counted exactly on both sides. -/
theorem hall_of_degree_comparison {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) [DecidableRel r] (hpos : ∀a,0<(univ.filter (r a)).card)
    (hdeg : ∀a b,r a b → (univ.filter (fun a => r a b)).card≤(univ.filter (r a)).card) :
    ∀S : Finset A,S.card≤(univ.filter (fun b => ∃a∈S,r a b)).card := by
  classical
  let da := fun a => (univ.filter (r a)).card
  let db := fun b => (univ.filter (fun a => r a b)).card
  intro S
  let T := univ.filter (fun b => ∃a∈S,r a b)
  let w : A → B → ℝ := fun a b => if r a b then 1/(da a:ℝ) else 0
  have hrow : ∀a∈S,(∑b∈T,w a b)=1 := by
    intro a ha
    have hsub : univ.filter (r a)⊆T := by
      intro b hb
      exact mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hb).2⟩
    have heq : T.filter (r a)=univ.filter (r a) := by
      ext b
      simp only [mem_filter,mem_univ,true_and]
      exact ⟨fun h => h.2,fun h => ⟨hsub (mem_filter.mpr ⟨mem_univ _,h⟩),h⟩⟩
    have hda : (0:ℝ)<(da a:ℝ) := by exact_mod_cast hpos a
    dsimp [w]
    rw [←sum_filter,heq,sum_const,nsmul_eq_mul]
    change (da a:ℝ)*(1/(da a:ℝ))=1
    exact mul_one_div_cancel (ne_of_gt hda)
  have hcol : ∀b∈T,(∑a∈S,w a b)≤1 := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := (mem_filter.mp hb).2
    have hdbNat : 0<db b := card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,hab⟩⟩
    have hdb : (0:ℝ)<(db b:ℝ) := by exact_mod_cast hdbNat
    have hweight : ∀a∈S,w a b≤(if r a b then 1/(db b:ℝ) else 0) := by
      intro a _
      dsimp [w]
      split_ifs with hab
      · have hh : (db b:ℝ)≤(da a:ℝ) := by exact_mod_cast hdeg a b hab
        exact one_div_le_one_div_of_le hdb hh
      · exact le_rfl
    have hs := sum_le_sum hweight
    have heq : (∑a∈S,if r a b then 1/(db b:ℝ) else 0)=
        ((S.filter fun a => r a b).card:ℝ)*(1/(db b:ℝ)) := by
      rw [←sum_filter,sum_const,nsmul_eq_mul]
    rw [heq] at hs
    have hcnt : (S.filter fun a => r a b).card≤db b := card_le_card
      (fun a ha => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
    have hcntR : ((S.filter fun a => r a b).card:ℝ)≤(db b:ℝ) := by exact_mod_cast hcnt
    exact hs.trans ((mul_le_mul_of_nonneg_right hcntR (by positivity)).trans_eq
      (mul_one_div_cancel (ne_of_gt hdb)))
  have hsum : (S.card:ℝ)≤(T.card:ℝ) := by
    calc
      _ = ∑a∈S,(∑b∈T,w a b) := by rw [sum_congr rfl hrow];simp
      _ = ∑b∈T,(∑a∈S,w a b) := sum_comm
      _ ≤ ∑_b∈T,(1:ℝ) := sum_le_sum hcol
      _ = _ := by simp
  exact_mod_cast hsum

/-- Degree comparison constructs an actual injective selection of neighbours. -/
theorem exists_injection_of_degree_comparison {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) [DecidableRel r] (hpos : ∀a,0<(univ.filter (r a)).card)
    (hdeg : ∀a b,r a b → (univ.filter (fun a => r a b)).card≤(univ.filter (r a)).card) :
    ∃f : A → B,Function.Injective f ∧ ∀a,r a (f a) := by
  classical
  exact (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp
    (hall_of_degree_comparison r hpos hdeg)

/-- Strict degree comparison supplies a disjoint matching after
removing any chosen injection supported on the relation. -/
theorem exists_second_injection_of_strict_degree_comparison
    {A B : Type*} [Fintype A] [Fintype B] (r : A → B → Prop) [DecidableRel r]
    (hpos : ∀a,0<(univ.filter (r a)).card)
    (hdeg : ∀a b,r a b → (univ.filter (fun a => r a b)).card<(univ.filter (r a)).card)
    (f : A → B) (hfr : ∀a,r a (f a)) :
    ∃g : A → B,Function.Injective g ∧ (∀a,r a (g a)) ∧ ∀a,f a≠g a := by
  classical
  let r' := fun a b => r a b ∧ b≠f a
  have hrow : ∀a,(univ.filter (r' a)).card+1=(univ.filter (r a)).card := by
    intro a
    have heq : univ.filter (r' a)=(univ.filter (r a)).erase (f a) := by
      ext b
      simp only [mem_filter,mem_univ,true_and,mem_erase,r']
      tauto
    rw [heq,card_erase_of_mem (mem_filter.mpr ⟨mem_univ _,hfr a⟩)]
    have hh := hpos a
    omega
  have hpos' : ∀a,0<(univ.filter (r' a)).card := by
    intro a
    have hcol : 0<(univ.filter (fun a' => r a' (f a))).card :=
      card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,hfr a⟩⟩
    have hh := hdeg a (f a) (hfr a)
    have hr := hrow a
    omega
  have hdeg' : ∀a b,r' a b → (univ.filter (fun a => r' a b)).card≤(univ.filter (r' a)).card := by
    intro a b hab
    have hs : univ.filter (fun a => r' a b)⊆univ.filter (fun a => r a b) := by
      intro a' ha'
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha').2.1⟩
    have hc := card_le_card hs
    have hh := hdeg a b hab.1
    have hr := hrow a
    omega
  obtain ⟨g,hg,hgr⟩ := exists_injection_of_degree_comparison r' hpos' hdeg'
  exact ⟨g,hg,fun a => (hgr a).1,fun a => (hgr a).2.symm⟩

/-- Strict degree comparison survives removal of the first transversal,
so two pointwise disjoint transversals are constructed. -/
theorem exists_two_injections_of_strict_degree_comparison
    {A B : Type*} [Fintype A] [Fintype B] (r : A → B → Prop) [DecidableRel r]
    (hpos : ∀a,0<(univ.filter (r a)).card)
    (hdeg : ∀a b,r a b → (univ.filter (fun a => r a b)).card<(univ.filter (r a)).card) :
    ∃f g : A → B,Function.Injective f ∧ Function.Injective g ∧
      (∀a,r a (f a)) ∧ (∀a,r a (g a)) ∧ ∀a,f a≠g a := by
  classical
  obtain ⟨f,hf,hfr⟩ := exists_injection_of_degree_comparison r hpos (fun a b h => (hdeg a b h).le)
  obtain ⟨g,hg,hgr,hfg⟩ := exists_second_injection_of_strict_degree_comparison r hpos hdeg f hfr
  exact ⟨f,g,hf,hg,hfr,hgr,hfg⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Turn an injective selection across a vertex cut into an ambient graph. -/
noncomputable def selectionGraph (W : Finset V) (f : W → ↥(Wᶜ : Finset V)) : SimpleGraph V where
  Adj u v := (∃a:W,u=a.val ∧ v=(f a).val) ∨ (∃a:W,v=a.val ∧ u=(f a).val)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨a,hu,hf⟩|⟨a,hu,hf⟩
    all_goals exact (mem_compl.mp (f a).property) (hf ▸ hu ▸ a.property)⟩

noncomputable instance (W : Finset V) (f : W → ↥(Wᶜ : Finset V)) :
    DecidableRel (selectionGraph W f).Adj := Classical.decRel _

private theorem selectionGraph_adj_left (W : Finset V) (f : W → ↥(Wᶜ : Finset V))
    {u v : V} (hu : u∈W) : (selectionGraph W f).Adj u v ↔ v=(f ⟨u,hu⟩).val := by
  constructor
  · rintro (⟨a,ha,hv⟩|⟨a,ha,hv⟩)
    · have he : a=⟨u,hu⟩ := Subtype.ext ha.symm
      simpa only [he] using hv
    · exact False.elim ((mem_compl.mp (f a).property) (hv ▸ hu))
  · intro hv
    exact Or.inl ⟨⟨u,hu⟩,rfl,hv⟩

/-- The constructed ambient graph is a matching and covers the whole left side. -/
theorem selectionGraph_isMatching (W : Finset V) (f : W → ↥(Wᶜ : Finset V)) (hf : Function.Injective f) :
    OneFactor.IsMatchingGraph (selectionGraph W f) ∧
      ∀w∈W,∃!v,(selectionGraph W f).Adj w v := by
  constructor
  · intro u v z huv huz
    by_cases hu : u∈W
    · exact ((selectionGraph_adj_left W f hu).mp huv).trans
        ((selectionGraph_adj_left W f hu).mp huz).symm
    · rcases huv with ⟨a,ha,_⟩|⟨a,hv,hfa⟩
      · exact False.elim (hu (ha ▸ a.property))
      rcases huz with ⟨b,hb,_⟩|⟨b,hz,hfb⟩
      · exact False.elim (hu (hb ▸ b.property))
      have he : a=b := hf (Subtype.ext (hfa.symm.trans hfb))
      exact hv.trans ((congrArg Subtype.val he).trans hz.symm)
  · intro w hw
    refine ⟨(f ⟨w,hw⟩).val,(selectionGraph_adj_left W f hw).mpr rfl,?_⟩
    exact fun v hv => (selectionGraph_adj_left W f hw).mp hv

/-- Edges of the selection graph are exactly the selected graph edges. -/
theorem selectionGraph_le {G : SimpleGraph V} (W : Finset V) (f : W → ↥(Wᶜ : Finset V))
    (hf : ∀a:W,G.Adj a.val (f a).val) : selectionGraph W f≤G := by
  intro u v h
  rcases h with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩
  · exact hf a
  · exact (hf a).symm

/-- Pointwise distinct injections produce edge-disjoint ambient matchings. -/
theorem selectionGraph_disjoint (W : Finset V) (f g : W → ↥(Wᶜ : Finset V))
    (hfg : ∀a,f a≠g a) : Disjoint (selectionGraph W f) (selectionGraph W g) := by
  apply disjoint_iff_inf_le.mpr
  intro u v ⟨huf,hug⟩
  have hbad : False := by
    by_cases hu : u∈W
    · have hf := (selectionGraph_adj_left W f hu).mp huf
      have hg := (selectionGraph_adj_left W g hu).mp hug
      exact hfg ⟨u,hu⟩ (Subtype.ext (hf.symm.trans hg))
    · have hufCopy := huf
      rcases huf with ⟨a,ha,_⟩|⟨a,hv,_⟩
      · exact hu (ha ▸ a.property)
      have hvW : v∈W := hv ▸ a.property
      have hf := (selectionGraph_adj_left W f hvW).mp ((selectionGraph W f).adj_symm hufCopy)
      have hg := (selectionGraph_adj_left W g hvW).mp ((selectionGraph W g).adj_symm hug)
      exact hfg ⟨v,hvW⟩ (Subtype.ext (hf.symm.trans hg))
  exact hbad.elim

/-- Every selected edge crosses the prescribed vertex cut. -/
theorem selectionGraph_crosses_cut (W : Finset V) (f : W → ↥(Wᶜ : Finset V))
    {u v : V} (huv : (selectionGraph W f).Adj u v) :
    (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W) := by
  rcases huv with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩
  · exact Or.inl ⟨a.property,mem_compl.mp (f a).property⟩
  · exact Or.inr ⟨a.property,mem_compl.mp (f a).property⟩

/-- The degree-comparison argument gives two actual edge-disjoint
matchings across a prescribed vertex cut. -/
theorem exists_two_matchings_of_strict_comparison (G : SimpleGraph V)
    (W : Finset V)
    (hpos : ∀a:W,0<(univ.filter fun b:↥(Wᶜ : Finset V) => G.Adj a.val b.val).card)
    (hdeg : ∀(a:W)(b:↥(Wᶜ : Finset V)),G.Adj a.val b.val →
      (univ.filter fun a':W => G.Adj a'.val b.val).card<
        (univ.filter fun b':↥(Wᶜ : Finset V) => G.Adj a.val b'.val).card) :
    ∃M₁ M₂ : SimpleGraph V,M₁≤G ∧ M₂≤G ∧
      OneFactor.IsMatchingGraph M₁ ∧ OneFactor.IsMatchingGraph M₂ ∧ Disjoint M₁ M₂ ∧
      (∀w∈W,∃!v,M₁.Adj w v) ∧ (∀w∈W,∃!v,M₂.Adj w v) ∧
      (∀u v,M₁.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W)) ∧
      (∀u v,M₂.Adj u v → (u∈W ∧ v∉W) ∨ (v∈W ∧ u∉W)) := by
  classical
  let r := fun (a:W) (b:↥(Wᶜ : Finset V)) => G.Adj a.val b.val
  obtain ⟨f,g,hf,hg,hfr,hgr,hfg⟩ :=
    exists_two_injections_of_strict_degree_comparison r hpos hdeg
  exact ⟨selectionGraph W f,selectionGraph W g,selectionGraph_le W f hfr,
    selectionGraph_le W g hgr,(selectionGraph_isMatching W f hf).1,
    (selectionGraph_isMatching W g hg).1,selectionGraph_disjoint W f g hfg,
    (selectionGraph_isMatching W f hf).2,(selectionGraph_isMatching W g hg).2,
    fun _ _ h => selectionGraph_crosses_cut W f h,
    fun _ _ h => selectionGraph_crosses_cut W g h⟩

/-- The low set used in the trimming step: degree at most one third
of the actual maximum degree. -/
def lowVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => 3*G.degree v≤G.maxDegree

/-- VAL proves the strict Hall comparison at every low-to-high edge. -/
theorem low_vertex_Hall_property (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) {w v : V} (_hw : w∈lowVertices G) (hwv : G.Adj w v) :
    ((G.neighborFinset v).filter fun z => z∈lowVertices G).card<G.degree w := by
  obtain ⟨a,b,hab⟩ := MaximumCoreTwo.exists_adj_of_not_colorable G hcrit.2.1
  have hD : 0<G.maxDegree :=
    ((G.degree_pos_iff_exists_adj a).mpr ⟨b,hab⟩).trans_le (G.degree_le_maxDegree a)
  have hlowNonmax : ∀z∈lowVertices G,G.degree z≠G.maxDegree := by
    intro z hz he
    have hh := (mem_filter.mp hz).2
    rw [he] at hh
    omega
  let L := (G.neighborFinset v).filter fun z => z∈lowVertices G
  let C := (G.neighborFinset v).filter fun z => G.degree z=G.maxDegree
  have hdis : Disjoint L C := Finset.disjoint_left.mpr (by
    intro z hzL hzC
    exact hlowNonmax z (mem_filter.mp hzL).2 (mem_filter.mp hzC).2)
  have hsub : L∪C⊆G.neighborFinset v := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdis,card_neighborFinset_eq_degree] at hcard
  have hval := Gate8J2C.deficit_le_maximumNeighbours G hcrit hwv.symm
  change G.maxDegree-G.degree w+1≤C.card at hval
  have hwD := G.degree_le_maxDegree w
  have hvD := G.degree_le_maxDegree v
  change L.card<G.degree w
  omega

/-- Chen--McDonald--Shan Lemma 3.4 for the concrete low-degree set:
two edge-disjoint graph matchings each saturate every low vertex.
All Hall obligations follow from criticality and VAL. -/
theorem exists_two_matchings_saturating_low_vertices (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcrit : IsDeltaCritical G) :
    ∃M₁ M₂ : SimpleGraph V,M₁≤G ∧ M₂≤G ∧
      OneFactor.IsMatchingGraph M₁ ∧ OneFactor.IsMatchingGraph M₂ ∧ Disjoint M₁ M₂ ∧
      (∀w∈lowVertices G,∃!v,M₁.Adj w v) ∧
      (∀w∈lowVertices G,∃!v,M₂.Adj w v) ∧
      (∀u v,M₁.Adj u v → (u∈lowVertices G ∧ v∉lowVertices G) ∨
        (v∈lowVertices G ∧ u∉lowVertices G)) ∧
      (∀u v,M₂.Adj u v → (u∈lowVertices G ∧ v∉lowVertices G) ∨
        (v∈lowVertices G ∧ u∉lowVertices G)) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v)))
  let W := lowVertices G
  obtain ⟨a,b,hab⟩ := MaximumCoreTwo.exists_adj_of_not_colorable G hcrit.2.1
  have hactive : ∀w,0<G.degree w := by
    intro w
    exact (G.degree_pos_iff_exists_adj w).mpr
      (MaximumCoreTwo.exists_adj_of_connected hcrit.1 hab w)
  have hind : ∀u∈W,∀v∈W,¬G.Adj u v := by
    intro u hu v hv huv
    have hsum := Overfull.deg_add hcrit huv
    have huD := (mem_filter.mp hu).2
    have hvD := (mem_filter.mp hv).2
    omega
  have hrow : ∀a:W,(univ.filter fun b:↥(Wᶜ : Finset V) => G.Adj a.val b.val).card=G.degree a.val := by
    intro a
    rw [DenseHall.subtype_filter_card,←card_neighborFinset_eq_degree]
    congr 1
    ext b
    simp only [mem_filter,mem_compl,mem_neighborFinset]
    exact ⟨fun h => h.2,fun h => ⟨fun hb => hind a.val a.property b hb h,h⟩⟩
  have hcol : ∀b:↥(Wᶜ : Finset V),(univ.filter fun a:W => G.Adj a.val b.val).card=
      ((G.neighborFinset b.val).filter fun z => z∈W).card := by
    intro b
    have hcast := DenseHall.subtype_filter_card W (fun a => G.Adj a b.val)
    calc
      _ = (W.filter fun a => G.Adj a b.val).card := by
        convert hcast using 1
      _ = _ := by
        congr 1
        ext a
        simp only [mem_filter,mem_neighborFinset]
        exact ⟨fun h => ⟨h.2.symm,h.1⟩,fun h => ⟨h.2,h.1.symm⟩⟩
  apply exists_two_matchings_of_strict_comparison G W
  · intro a
    rw [hrow]
    exact hactive a.val
  · intro a b hab
    rw [hcol,hrow]
    exact low_vertex_Hall_property G hcrit a.property hab

/-- The union of two disjoint matchings has an actual two-edge-colouring
and its degrees are the sums of the two matching degrees. -/
theorem two_matching_union_colouring (M₁ M₂ : SimpleGraph V)
    [DecidableRel M₁.Adj] [DecidableRel M₂.Adj]
    (hm₁ : OneFactor.IsMatchingGraph M₁) (hm₂ : OneFactor.IsMatchingGraph M₂)
    (hdis : Disjoint M₁ M₂) :
    (M₁⊔M₂).EdgeColorable 2 ∧
      (∀v,(M₁⊔M₂).degree v=M₁.degree v+M₂.degree v) ∧
      ∀v,(M₁⊔M₂).degree v≤2 := by
  classical
  have hbot : (⊥ : SimpleGraph V).EdgeColorable 0 := by
    have : IsEmpty (⊥ : SimpleGraph V).edgeSet := ⟨fun e => by simpa using e.property⟩
    exact Colorable.of_isEmpty 0
  have hc₁ : M₁.EdgeColorable 1 := by
    have hh : ((⊥ : SimpleGraph V)⊔M₁).EdgeColorable 1 :=
      OneFactor.colorable_sup_matching disjoint_bot_left hm₁ hbot
    exact Critical.colourable_of_copy (Copy.ofLE M₁ (⊥⊔M₁) le_sup_right) hh
  have hc₂ : (M₁⊔M₂).EdgeColorable 2 := OneFactor.colorable_sup_matching hdis hm₂ hc₁
  have hadd : ∀v,(M₁⊔M₂).degree v=M₁.degree v+M₂.degree v := by
    intro v
    rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
      card_union_of_disjoint (disjoint_neighborFinset_of_disjoint M₁ M₂ v hdis),
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]
  have hdeg₁ : ∀v,M₁.degree v≤1 := by
    intro v
    rw [←card_neighborFinset_eq_degree]
    exact card_le_one.mpr (fun a ha b hb => hm₁ v a b
      ((mem_neighborFinset _ _ _).mp ha) ((mem_neighborFinset _ _ _).mp hb))
  have hdeg₂ : ∀v,M₂.degree v≤1 := by
    intro v
    rw [←card_neighborFinset_eq_degree]
    exact card_le_one.mpr (fun a ha b hb => hm₂ v a b
      ((mem_neighborFinset _ _ _).mp ha) ((mem_neighborFinset _ _ _).mp hb))
  exact ⟨hc₂,hadd,fun v => by rw [hadd];have := hdeg₁ v;have := hdeg₂ v;omega⟩

/-- A genuine two-colour layer absorbs two incidences at every low
vertex, uses only edges crossing the low-set cut, and has degree at most
two everywhere. No matching or colouring is assumed as an input. -/
theorem exists_two_colour_low_absorber (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) :
    ∃H : SimpleGraph V,H≤G ∧ H.EdgeColorable 2 ∧
      (∀w∈lowVertices G,H.degree w=2) ∧ (∀v,H.degree v≤2) ∧
      ∀u v,H.Adj u v → (u∈lowVertices G ∧ v∉lowVertices G) ∨
        (v∈lowVertices G ∧ u∉lowVertices G) := by
  classical
  obtain ⟨M₁,M₂,hM₁,hM₂,hm₁,hm₂,hdis,hcover₁,hcover₂,hcross₁,hcross₂⟩ :=
    exists_two_matchings_saturating_low_vertices G hcrit
  obtain ⟨hc,hadd,hmax⟩ := two_matching_union_colouring M₁ M₂ hm₁ hm₂ hdis
  refine ⟨M₁⊔M₂,sup_le hM₁ hM₂,hc,?_,?_,?_⟩
  · intro w hw
    have hh : (M₁⊔M₂).degree w=2 := by
      rw [hadd,degree_eq_one_iff_existsUnique_adj.mpr (hcover₁ w hw),
        degree_eq_one_iff_existsUnique_adj.mpr (hcover₂ w hw)]
    convert hh using 1
    congr 5
    exact Subsingleton.elim _ _
  · intro v
    convert hmax v using 1
    congr 5
    exact Subsingleton.elim _ _
  · intro u v huv
    rcases huv with h|h
    · exact hcross₁ u v h
    · exact hcross₂ u v h

end OverfullWork.LowVertexMatchingAbsorption
