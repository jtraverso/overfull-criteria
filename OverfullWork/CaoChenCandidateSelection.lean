module

public import OverfullWork.CaoChenSecondarySpineNormalization
public import OverfullWork.CaoChenFinitePaletteProgress

@[expose] public section


/-! # Actual candidate selection and secondary low-leaf preparation

Below score k, a selected palette of size 3k has k+1 colours outside
both root-missing and protected colours. Either one is missing at the
spine, or a real secondary normalization creates a low leaf with a common
root colour outside both protected and selected palettes. All numerical
bounds depend only on k and the current primary overlap threshold.
-/
namespace OverfullWork.CaoChenCandidateSelection
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenOverlapNormalization CaoChenPaletteOverlapNormalization
open CaoChenSecondaryNormalization CaoChenSecondarySpineNormalization CaoChenFinitePaletteProgress
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- A graph-independent upper bound for both protected boundary costs. -/
def secondaryBudget (k M : ℕ) : ℕ :=
  4*k+3+(2*k+4)*(k+1)+(M+2)*(3*k+1)

def protectedFamily (α : Fin G.maxDegree) (T F : Finset (Fin G.maxDegree)) : Finset (Fin G.maxDegree) :=
  insert α (T∪F)

/-- Counting the two forbidden parts constructs k+1 actual candidates. -/
theorem exists_candidates {A : Type*} [DecidableEq A] (k : ℕ) (T X F : Finset A)
    (hcard : T.card=3*k) (hscore : (T∩X).card<k) (hprotected : (T∩F).card≤k) :
    ∃Tau : Finset A,Tau⊆T\(X∪F) ∧ Tau.card=k+1 := by
  have he : T∩(X∪F)=(T∩X)∪(T∩F) := by ext a;simp only [mem_inter,mem_union];tauto
  have hc:=card_union_le (T∩X) (T∩F)
  rw [←he] at hc
  have hs:=card_sdiff_add_card_inter T (X∪F)
  have hroom : k+1≤(T\(X∪F)).card := by omega
  exact exists_subset_card_eq hroom

/-- Exact metadata for the actual secondary output colouring. -/
structure SecondaryCandidate (c₀ c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y z u : V) (α β : Fin G.maxDegree) (T F Tau : Finset (Fin G.maxDegree)) (k M : ℕ) : Prop where
  normalization : State c₀ c x y (protectedFamily α T F) (missing c₀ x)
    (paletteLeaves c₀ q x y (insert α T)) M
  selected : T⊆badColours c q u∩paletteS c q x y
  rootSpine : c.col x u=some β
  initialSpine : c.col x z=some α
  score : (T∩missing c x).card=(T∩missing c₀ x).card
  primaryColours : smallRootOverlapColours c q x y (insert α T) M⊆
    smallRootOverlapColours c₀ q x y (insert α T) M
  rolePreserved : SpineRole c₀ q x y α M → SpineRole c q x y α M
  candidate : ∃η∈Tau,∃t : V,c.col u t=some η ∧ t≠x ∧ (G.degree t:ℝ)<q ∧
    F.card+k<(missing c t∩missing c x).card ∧
    ∃δ : Fin G.maxDegree,c.IsFree x δ ∧ c.IsFree t δ ∧ δ∉F ∧ δ∉T

/-- The all-present branch performs the actual secondary normalization.
The candidate family is supplied only as an explicitly selected subset;
no large-overlap leaf or output colouring is assumed. -/
theorem exists_secondary_candidate_of_all_present (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y z u : V} {α β : Fin G.maxDegree}
    (hcm₀ : IsColMinus c₀ x y) (hxu : c₀.col x u=some β) (hxz : c₀.col x z=some α)
    (T F Tau : Finset (Fin G.maxDegree)) (k M : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hT : T⊆badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) u∩paletteS c₀ ((1-ε)*(G.maxDegree:ℝ)) x y)
    (hcard : T.card=3*k) (hscore : (T∩missing c₀ x).card<k) (hFcard : F.card≤k+2)
    (hβ : β∉T) (hTau : Tau⊆T\(missing c₀ x∪F)) (hTaucard : Tau.card=k+1)
    (hpresent : ∀η∈Tau,¬c₀.IsFree u η)
    (hL : 1≤ε*((k+1:ℕ):ℝ))
    (hthreshold : ((2*k+2:ℕ):ℝ)+(k:ℝ)*((secondaryBudget k M+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : secondaryBudget k M+(k+1)*(2*k+2)<(missing c₀ x).card) :
    ∃c : PEC G (Fin G.maxDegree),SecondaryCandidate c₀ c ((1-ε)*(G.maxDegree:ℝ))
      x y z u α β T F Tau k M := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let C:=insert α T
  let Full:=protectedFamily α T F
  let m:=F.card+k
  let S:=spokeLeaves c₀ u Tau
  let A:=paletteLeaves c₀ q x y C
  have hTauT : Tau⊆T:=fun η hη => (mem_sdiff.mp (hTau hη)).1
  have hTauLow : Tau⊆lowColours c₀ q u := by
    intro η hη
    have hbad:=(mem_inter.mp (hT (hTauT hη))).1
    obtain ⟨v,huv,hvlow⟩:=((mem_badColours c₀ q u η).mp hbad).resolve_left (hpresent η hη)
    exact (mem_lowColours c₀ q u η).mpr ⟨v,huv,hvlow⟩
  have hSCard : S.card=k+1 := by
    rw [←hTaucard]
    apply CaoChenPaletteCounting.card_leaves_eq_card_colours u S Tau
    · intro v hv
      exact (mem_filter.mp hv).2
    · intro η hη
      obtain ⟨v,huv,_⟩:=(mem_lowColours c₀ q u η).mp (hTauLow hη)
      exact ⟨v,mem_filter.mpr ⟨mem_univ v,η,hη,huv⟩,huv⟩
  have hSlow : ∀v∈S,(G.degree v:ℝ)<q := by
    intro v hv
    obtain ⟨η,hη,huv⟩:=(mem_filter.mp hv).2
    obtain ⟨w,huw,hwlow⟩:=(mem_lowColours c₀ q u η).mp (hTauLow hη)
    have he : v=w:=c₀.col_proper huv huw
    subst w
    exact hwlow
  have hCcard : C.card≤3*k+1 := by
    have hc:=card_insert_le α T
    dsimp [C]
    omega
  have hAcard : A.card≤3*k+1 := by
    have he : A.card=(C∩paletteA c₀ q x y).card:=paletteLeaves_card_eq c₀ q x y C
    exact (he.le.trans (card_le_card inter_subset_left)).trans hCcard
  have hFullcard : Full.card≤4*k+3 := by
    have hi:=card_insert_le α (T∪F)
    have hu:=card_union_le T F
    change Full.card≤(T∪F).card+1 at hi
    omega
  have hm : m≤2*k+2 := by dsimp [m];omega
  have hB : Full.card+(m+2)*S.card+(M+2)*A.card≤secondaryBudget k M := by
    have hmulS:=Nat.mul_le_mul_right (k+1) (show m+2≤2*k+4 by omega)
    have hmulA:=Nat.mul_le_mul_left (M+2) hAcard
    rw [hSCard]
    dsimp [secondaryBudget]
    omega
  have hthreshold' : (m:ℝ)+((S.card-1:ℕ):ℝ)*
      ((Full.card+(m+2)*S.card+(M+2)*A.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    have hmR : (m:ℝ)≤((2*k+2:ℕ):ℝ):=by exact_mod_cast hm
    have hBR : ((Full.card+(m+2)*S.card+(M+2)*A.card+1:ℕ):ℝ)≤
        ((secondaryBudget k M+1:ℕ):ℝ) := by exact_mod_cast (show _≤_ by omega)
    rw [hSCard] at hBR
    have hmul:=mul_le_mul_of_nonneg_left hBR (Nat.cast_nonneg k : (0:ℝ)≤_)
    rw [hSCard,Nat.add_sub_cancel] 
    linarith only [hmR,hmul,hthreshold]
  have hbudget' : Full.card+(m+2)*S.card+(M+2)*A.card+S.card*m<(missing c₀ x).card := by
    have hmul:=Nat.mul_le_mul_left (k+1) hm
    rw [hSCard] at hB ⊢
    omega
  obtain ⟨c,hs,hsmall⟩:=exists_root_overlap_normalization_preserving_primary hG c₀ hcm₀
    S A Full (missing c₀ x) m M (k+1) ε hε hεone hx hSlow hL hthreshold' hbudget'
  have hTFull : T⊆Full:=fun η hη => mem_insert_of_mem (mem_union_left F hη)
  have hTauFull : Tau⊆Full:=hTauT.trans hTFull
  have hCFull : C⊆Full := by
    intro η hη
    rcases mem_insert.mp hη with rfl|hηT
    · exact mem_insert_self _ _
    · exact hTFull hηT
  have hselected : T⊆badColours c q u∩paletteS c q x y := by
    intro η hη
    obtain ⟨hbad,hS⟩:=mem_inter.mp (hT hη)
    exact mem_inter.mpr ⟨(bad_role_iff hs q u η (hTFull hη)).mpr hbad,
      (S_role_iff hs q η (hTFull hη)).mpr hS⟩
  have hroot : missing c x=missing c₀ x := by
    ext η
    simp only [mem_missing,IsFree]
    simp_rw [hs.rootRow]
  have hsmallColours : (smallSpokeColours c x u Tau m).card<k+1 := by
    have hcount : (lowOverlapVertices c (missing c x) S m).card=
        (smallSpokeColours c x u Tau m).card := by
      apply CaoChenPaletteCounting.card_leaves_eq_card_colours u
        (lowOverlapVertices c (missing c x) S m) (smallSpokeColours c x u Tau m)
      · intro v hv
        obtain ⟨hvS,hvsmall⟩:=mem_filter.mp hv
        obtain ⟨η,hη,huv₀⟩:=(mem_filter.mp hvS).2
        have huv : c.col u v=some η:=(hs.protectedColours u v η (hTauFull hη)).mpr huv₀
        exact ⟨η,mem_filter.mpr ⟨hη,v,huv,hvsmall⟩,huv⟩
      · intro η hη
        obtain ⟨hηTau,v,huv,hvsmall⟩:=mem_filter.mp hη
        have huv₀ : c₀.col u v=some η:=(hs.protectedColours u v η (hTauFull hηTau)).mp huv
        exact ⟨v,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ v,η,hηTau,huv₀⟩,hvsmall⟩,huv⟩
    rwa [←hcount]
  have hroom : (smallSpokeColours c x u Tau m).card<Tau.card:=by omega
  obtain ⟨η,hηTau,hηnot⟩:=exists_mem_notMem_of_card_lt_card hroom
  obtain ⟨t,hut₀,htlow⟩:=(mem_lowColours c₀ q u η).mp (hTauLow hηTau)
  have hut : c.col u t=some η:=(hs.protectedColours u t η (hTauFull hηTau)).mpr hut₀
  have hlarge : m<(missing c t∩missing c x).card := by
    by_contra hn
    exact hηnot (mem_filter.mpr ⟨hηTau,t,hut,by omega⟩)
  have htx : t≠x := by
    intro he
    have hxu₀ : c₀.col x u=some η:=by rw [c₀.col_symm,←he];exact hut₀
    have heβ : β=η:=Option.some.inj (hxu.symm.trans hxu₀)
    exact hβ (heβ.symm ▸ hTauT hηTau)
  have hscoreEq : (T∩missing c x).card=(T∩missing c₀ x).card:=by rw [hroot]
  have hauxBudget : F.card+(T∩missing c x).card<(missing c t∩missing c x).card := by
    dsimp [m] at hlarge
    omega
  obtain ⟨δ,hδx,hδt,hδF,hδT⟩:=exists_common_root_auxiliary c x t F T hauxBudget
  refine ⟨c,⟨hs,hselected,?_,?_,hscoreEq,primary_colours_subset q hs hCFull,?_,?_⟩⟩
  · rw [hs.rootRow]
    exact hxu
  · rw [hs.rootRow]
    exact hxz
  · exact spineRole_preserved q hs hCFull (mem_insert_self _ _) hxz
  · exact ⟨η,hηTau,t,hut,htx,htlow,hlarge,δ,hδx,hδt,hδF,hδT⟩

/-- The complete candidate dichotomy: missing at the spine, or an actual
secondary output supplying a common-root auxiliary at a genuine low leaf. -/
theorem exists_candidate_or_secondary_leaf (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y z u : V} {α β : Fin G.maxDegree}
    (hcm₀ : IsColMinus c₀ x y) (hxu : c₀.col x u=some β) (hxz : c₀.col x z=some α)
    (T F : Finset (Fin G.maxDegree)) (k M : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hT : T⊆badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) u∩paletteS c₀ ((1-ε)*(G.maxDegree:ℝ)) x y)
    (hcard : T.card=3*k) (hscore : (T∩missing c₀ x).card<k)
    (hprotected : (T∩F).card≤k) (hFcard : F.card≤k+2) (hβ : β∉T)
    (hL : 1≤ε*((k+1:ℕ):ℝ))
    (hthreshold : ((2*k+2:ℕ):ℝ)+(k:ℝ)*((secondaryBudget k M+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : secondaryBudget k M+(k+1)*(2*k+2)<(missing c₀ x).card) :
    ∃Tau : Finset (Fin G.maxDegree),Tau⊆T\(missing c₀ x∪F) ∧ Tau.card=k+1 ∧
      ((∃η∈Tau,c₀.IsFree u η) ∨ ∃c : PEC G (Fin G.maxDegree),
        SecondaryCandidate c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y z u α β T F Tau k M) := by
  obtain ⟨Tau,hTau,hTaucard⟩:=exists_candidates k T (missing c₀ x) F hcard hscore hprotected
  refine ⟨Tau,hTau,hTaucard,?_⟩
  by_cases hmiss : ∃η∈Tau,c₀.IsFree u η
  · exact Or.inl hmiss
  · right
    have hpresent : ∀η∈Tau,¬c₀.IsFree u η := by
      intro η hη hfree
      exact hmiss ⟨η,hη,hfree⟩
    exact exists_secondary_candidate_of_all_present hG c₀ hcm₀ hxu hxz T F Tau k M ε hε hεone hx
      hT hcard hscore hFcard hβ hTau hTaucard hpresent hL hthreshold hbudget

end OverfullWork.CaoChenCandidateSelection
