module

public import OverfullWork.CaoChenForkSelection
public import OverfullWork.CommonMissingColour
public import OverfullWork.CaoChenSelectedGeometry

@[expose] public section


/-! # Kempe assembly for Cao--Chen Proposition A, Claim 5.4

The missing-colour and Kempe-chain constructions act on actual partial
colourings. A-coloured edges retain A-membership under the permitted
swaps, while the spine remains rooted at the same vertex.
-/
namespace OverfullWork.CaoChenForkAssembly
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenForkCounting CaoChenForkSelection
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

omit [DecidableEq V] in
theorem inA_swap_iff {c : PEC G (Fin G.maxDegree)} {a b : V}
    {θ η : Fin G.maxDegree} (hθ : InA c a b θ) (hη : InA c a b η) (γ : Fin G.maxDegree) :
    InA c a b (Equiv.swap θ η γ) ↔ InA c a b γ := by
  by_cases he : γ=θ
  · subst γ
    simp only [Equiv.swap_apply_left]
    exact iff_of_true hη hθ
  by_cases hf : γ=η
  · subst γ
    simp only [Equiv.swap_apply_right]
    exact iff_of_true hθ hη
  rw [Equiv.swap_apply_of_ne_of_ne he hf]

theorem inA_permCol_swap_iff {c : PEC G (Fin G.maxDegree)} {a b : V}
    {θ η : Fin G.maxDegree} (hθ : InA c a b θ) (hη : InA c a b η) (γ : Fin G.maxDegree) :
    InA (permCol c (Equiv.swap θ η)) a b γ ↔ InA c a b γ := by
  simpa only [InA,isFree_permCol,Equiv.symm_swap] using inA_swap_iff hθ hη γ

theorem rootedAdmissible_permCol {c : PEC G (Fin G.maxDegree)} {a b u : V}
    (hroot : RootedAdmissible c a b u) (σ : Equiv.Perm (Fin G.maxDegree)) :
    RootedAdmissible (permCol c σ) a b u := by
  obtain ⟨hcm,α,hcol,hfree⟩:=hroot
  refine ⟨hcm.permCol σ,σ α,?_,?_⟩
  · rw [permCol_col,hcol]
    rfl
  · rw [isFree_permCol]
    simpa only [Equiv.symm_apply_apply] using hfree

theorem rootedAdmissible_kempeSwap (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b u w : V} {θ η : Fin G.maxDegree}
    (hroot : RootedAdmissible c a b u) (hθ : InA c a b θ) (hη : InA c a b η)
    (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w≠a) (hwb : w≠b) :
    RootedAdmissible (c.kempeSwap θ η w) a b u := by
  obtain ⟨hcm,α,hcol,hfree⟩:=hroot
  have hfreeInv (γ : Fin G.maxDegree) :
      (c.kempeSwap θ η w).IsFree a γ ↔ c.IsFree a γ :=
    kempeSwap_keeps_ab hG hcm hθ hη hw hwa hwb (Or.inl rfl) γ
  refine ⟨hcm.kempeSwap θ η w,?_⟩
  by_cases hr : (c.kempeGraph θ η).Reachable w b
  · have hb : ¬c.IsFree b θ ∧ ¬c.IsFree b η := by
      rcases chain_avoids_ab hG hcm hθ hη hw hwa hwb (Or.inr rfl) with hn|hh
      · exact False.elim (hn hr)
      · exact hh
    refine ⟨Equiv.swap θ η α,?_,(hfreeInv _).mpr ?_⟩
    · rw [kempeSwap_col,kempeSwapFun_of_reachable c θ η hr u,hcol]
      rfl
    · by_cases he : α=θ
      · subst α
        rw [Equiv.swap_apply_left]
        exact hη.resolve_right hb.2
      by_cases hf : α=η
      · subst α
        rw [Equiv.swap_apply_right]
        exact hθ.resolve_right hb.1
      · rw [Equiv.swap_apply_of_ne_of_ne he hf]
        exact hfree
  · refine ⟨α,?_,(hfreeInv _).mpr hfree⟩
    rw [kempeSwap_col,kempeSwapFun_of_not_reachable c θ η hr u]
    exact hcol

theorem good_permCol_swap {c : PEC G (Fin G.maxDegree)} {a b x y : V}
    {θ η : Fin G.maxDegree} (hθ : InA c a b θ) (hη : InA c a b η)
    (hgood : Good c a b x y) : Good (permCol c (Equiv.swap θ η)) a b x y := by
  obtain ⟨γ,hcol,hA⟩:=hgood
  refine ⟨Equiv.swap θ η γ,?_,(inA_permCol_swap_iff hθ hη _).mpr ((inA_swap_iff hθ hη γ).mpr hA)⟩
  rw [permCol_col,hcol]
  rfl

theorem good_kempeSwap (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b w x y : V} {θ η : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hθ : InA c a b θ) (hη : InA c a b η)
    (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w≠a) (hwb : w≠b)
    (hgood : Good c a b x y) : Good (c.kempeSwap θ η w) a b x y := by
  obtain ⟨γ,hcol,hA⟩:=hgood
  have hInv (ζ : Fin G.maxDegree) := inA_kempeSwap_keeps hG hcm hθ hη hw hwa hwb ζ
  by_cases hr : (c.kempeGraph θ η).Reachable w x
  · refine ⟨Equiv.swap θ η γ,?_,(hInv _).mpr ((inA_swap_iff hθ hη γ).mpr hA)⟩
    rw [kempeSwap_col,kempeSwapFun_of_reachable c θ η hr y,hcol]
    rfl
  · refine ⟨γ,?_,(hInv _).mpr hA⟩
    rw [kempeSwap_col,kempeSwapFun_of_not_reachable c θ η hr y]
    exact hcol

theorem rootedAdmissible_kempeSwapCompl (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b u w : V} {θ η : Fin G.maxDegree}
    (hroot : RootedAdmissible c a b u) (hθ : InA c a b θ) (hη : InA c a b η)
    (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w≠a) (hwb : w≠b) :
    RootedAdmissible (kempeSwapCompl c θ η w) a b u := by
  have hpθ : InA (permCol c (Equiv.swap θ η)) a b θ := (inA_permCol_swap_iff hθ hη θ).mpr hθ
  have hpη : InA (permCol c (Equiv.swap θ η)) a b η := (inA_permCol_swap_iff hθ hη η).mpr hη
  have hpw : (permCol c (Equiv.swap θ η)).IsFree w θ ∨ (permCol c (Equiv.swap θ η)).IsFree w η := by
    rcases hw with hh|hh
    · right
      rw [isFree_permCol,Equiv.symm_swap,Equiv.swap_apply_right]
      exact hh
    · left
      rw [isFree_permCol,Equiv.symm_swap,Equiv.swap_apply_left]
      exact hh
  exact rootedAdmissible_kempeSwap hG (rootedAdmissible_permCol hroot _) hpθ hpη hpw hwa hwb

theorem good_kempeSwapCompl (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b w x y : V} {θ η : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hθ : InA c a b θ) (hη : InA c a b η)
    (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w≠a) (hwb : w≠b)
    (hgood : Good c a b x y) : Good (kempeSwapCompl c θ η w) a b x y := by
  have hpθ : InA (permCol c (Equiv.swap θ η)) a b θ := (inA_permCol_swap_iff hθ hη θ).mpr hθ
  have hpη : InA (permCol c (Equiv.swap θ η)) a b η := (inA_permCol_swap_iff hθ hη η).mpr hη
  have hpw : (permCol c (Equiv.swap θ η)).IsFree w θ ∨ (permCol c (Equiv.swap θ η)).IsFree w η := by
    rcases hw with hh|hh
    · right
      rw [isFree_permCol,Equiv.symm_swap,Equiv.swap_apply_right]
      exact hh
    · left
      rw [isFree_permCol,Equiv.symm_swap,Equiv.swap_apply_left]
      exact hh
  exact good_kempeSwap hG (hcm.permCol _) hpθ hpη hpw hwa hwb (good_permCol_swap hθ hη hgood)

/-- A finite family of small vertices, together with a, has a common
missing colour whenever its degree budget is below the palette size. -/
theorem exists_common_free_for_family {n d : ℕ} (c : PEC G (Fin G.maxDegree))
    (a : V) (t : Fin n → V) (hda : G.degree a≤d) (hdt : ∀ i,G.degree (t i)≤d)
    (hbudget : (n+1)*d<G.maxDegree) :
    ∃ δ : Fin G.maxDegree,c.IsFree a δ ∧ ∀ i,c.IsFree (t i) δ := by
  let T:=insert a (univ.image t)
  have hcard : T.card≤n+1 := by
    have hh:=card_insert_le a (univ.image t)
    have hi:=card_image_le (s:=(univ : Finset (Fin n))) (f:=t)
    simp only [card_univ,Fintype.card_fin] at hi
    change (insert a (univ.image t)).card≤n+1
    omega
  have hsum : (∑ v∈T,G.degree v)≤(n+1)*d := by
    calc
      _ ≤ ∑ _v∈T,d := by
        apply sum_le_sum
        intro v hv
        rcases mem_insert.mp hv with he|hv
        · subst v;exact hda
        · obtain ⟨i,_,rfl⟩:=mem_image.mp hv
          exact hdt i
      _ = T.card*d := by simp
      _ ≤ _ := Nat.mul_le_mul_right d hcard
  obtain ⟨δ,_,hδ⟩:=CommonMissingColour.exists_common_free_outside_of_degree_budget c T ∅ (by simpa using hsum.trans_lt hbudget)
  refine ⟨δ,hδ a (mem_insert_self _ _),?_⟩
  intro i
  exact hδ (t i) (mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ i,rfl⟩))

/-- A Kempe component containing one missing-colour leaf contains at
most one further leaf of an injective family missing the same colour. -/
theorem reachable_other_leaves_card_le_one {n : ℕ} (c : PEC G (Fin G.maxDegree))
    (t : Fin n → V) (ht : Function.Injective t) (j : Fin n)
    (θ η : Fin G.maxDegree) (hfree : ∀ i,c.IsFree (t i) η) :
    (((univ.erase j).filter fun i => (c.kempeGraph θ η).Reachable (t j) (t i))).card≤1 := by
  rw [card_le_one]
  intro i hi l hl
  obtain ⟨hi,hri⟩:=mem_filter.mp hi
  obtain ⟨hl,hrl⟩:=mem_filter.mp hl
  have hij:= (mem_erase.mp hi).1
  have hlj:= (mem_erase.mp hl).1
  by_contra hil
  exact not_three_linked c
    (fun h => hij (ht h).symm) (fun h => hlj (ht h).symm) (fun h => hil (ht h))
    (Or.inr (hfree j)) (Or.inr (hfree i)) (Or.inr (hfree l)) hri hrl

/-- The first Kempe operation in Claim 5.4 constructs a rooted colouring
in which at least d other selected leaves miss the first leaf's colour.
All selected anchor edges remain genuinely A-coloured. -/
theorem exists_many_leaves_missing_first_colour (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ)
    (hroot : RootedAdmissible c a b u) (hda : G.degree a≤d)
    (hdelta : (d+1)*(d+3)≤G.maxDegree)
    (z t : Fin (d+2) → V) (ht : Function.Injective t)
    (hta : ∀ i,t i≠a) (htb : ∀ i,t i≠b) (hdt : ∀ i,G.degree (t i)≤d)
    (hgoodU : ∀ i,Good c a b u (z i)) (hgoodE : ∀ i,Good c a b (z i) (t i)) :
    ∃ c' : PEC G (Fin G.maxDegree),RootedAdmissible c' a b u ∧
      (∀ i,Good c' a b u (z i)) ∧ (∀ i,Good c' a b (z i) (t i)) ∧
      ∃ θ : Fin G.maxDegree,∃ I : Finset (Fin (d+2)),
        c'.col (z 0) (t 0)=some θ ∧ InA c' a b θ ∧
        d≤I.card ∧ 0∉I ∧ ∀ i∈I,c'.IsFree (t i) θ := by
  obtain ⟨θ,hfirst,hθ⟩:=hgoodE 0
  have hb : (d+2+1)*d<G.maxDegree := by nlinarith only [hdelta]
  obtain ⟨δ,hδa,hδt⟩:=exists_common_free_for_family c a t hda hdt hb
  let c':=kempeSwapCompl c θ δ (t 0)
  have hδ : InA c a b δ:=Or.inl hδa
  have hw : c.IsFree (t 0) θ ∨ c.IsFree (t 0) δ:=Or.inr (hδt 0)
  have hroot' : RootedAdmissible c' a b u :=
    rootedAdmissible_kempeSwapCompl hG hroot hθ hδ hw (hta 0) (htb 0)
  have hgoodU' : ∀ i,Good c' a b u (z i) := fun i =>
    good_kempeSwapCompl hG hroot.1 hθ hδ hw (hta 0) (htb 0) (hgoodU i)
  have hgoodE' : ∀ i,Good c' a b (z i) (t i) := fun i =>
    good_kempeSwapCompl hG hroot.1 hθ hδ hw (hta 0) (htb 0) (hgoodE i)
  have hfirst' : c'.col (z 0) (t 0)=some θ := by
    rw [c'.col_symm]
    change (kempeSwapCompl c θ δ (t 0)).col (t 0) (z 0)=some θ
    rw [kempeSwapCompl_col_of_reachable c θ δ (SimpleGraph.Reachable.refl _) (z 0),c.col_symm]
    exact hfirst
  have hθ' : InA c' a b θ := by
    obtain ⟨γ,hcol,hA⟩:=hgoodE' 0
    have he : γ=θ:=Option.some.inj (hcol.symm.trans hfirst')
    simpa only [he] using hA
  let I:=((univ.erase (0:Fin (d+2))).filter fun i => ¬(c.kempeGraph θ δ).Reachable (t 0) (t i))
  have hinside:=reachable_other_leaves_card_le_one c t ht 0 θ δ hδt
  have hsplit:=card_filter_add_card_filter_not (s:=univ.erase (0:Fin (d+2)))
    (fun i => (c.kempeGraph θ δ).Reachable (t 0) (t i))
  change ((univ.erase (0:Fin (d+2))).filter (fun i => (c.kempeGraph θ δ).Reachable (t 0) (t i))).card+I.card=(univ.erase (0:Fin (d+2))).card at hsplit
  have htotal : (univ.erase (0:Fin (d+2))).card=d+1 := by simp
  have hI : d≤I.card := by omega
  refine ⟨c',hroot',hgoodU',hgoodE',θ,I,hfirst',hθ',hI,?_,?_⟩
  · intro hi
    exact (mem_erase.mp (mem_filter.mp hi).1).1 rfl
  · intro i hi
    have hn := (mem_filter.mp hi).2
    change (kempeSwapCompl c θ δ (t 0)).IsFree (t i) θ
    rw [kempeSwapCompl_isFree_of_not_reachable c θ δ hn,Equiv.swap_apply_left]
    exact hδt i

/-- A repeated A-colour on two leaves can be changed into a mutual
missing-colour pair by one actual Kempe swap. -/
theorem fork_of_repeated_leaf_colour (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) (a b u z₀ z₁ z₂ t₀ t₁ t₂ : V) (d : ℕ)
    (hroot : RootedAdmissible c a b u)
    (hseven₁ : Distinct7 a b u z₀ z₁ t₀ t₁)
    (hseven₂ : Distinct7 a b u z₀ z₂ t₀ t₂) (ht₁₂ : t₁≠t₂)
    (hda : G.degree a≤d) (hdt₀ : G.degree t₀≤d)
    (hdt₁ : G.degree t₁≤d) (hdt₂ : G.degree t₂≤d) (hbudget : 4*d<G.maxDegree)
    (hgood₀ : Good c a b u z₀) (hgood₁ : Good c a b u z₁) (hgood₂ : Good c a b u z₂)
    (θ ξ : Fin G.maxDegree) (he₀ : c.col z₀ t₀=some θ) (hθ : InA c a b θ)
    (he₁ : c.col z₁ t₁=some ξ) (he₂ : c.col z₂ t₂=some ξ) (hξ : InA c a b ξ)
    (hfree₁ : c.IsFree t₁ θ) (hfree₂ : c.IsFree t₂ θ) :
    ∃ c' : PEC G (Fin G.maxDegree),∃ z' t' : V,
      G.degree t'≤d ∧ Distinct7 a b u z₀ z' t₀ t' ∧
      ∃ α β₁ β₂ γ₁ γ₂,IsFork c' a b u z₀ z' t₀ t' α β₁ β₂ γ₁ γ₂ := by
  let f : Fin 3 → V:=![t₀,t₁,t₂]
  have hdf : ∀ i,G.degree (f i)≤d := by
    intro i
    fin_cases i
    · exact hdt₀
    · exact hdt₁
    · exact hdt₂
  obtain ⟨δ,hδa,hδf⟩:=exists_common_free_for_family c a f hda hdf (by simpa using hbudget)
  have hδ₀ : c.IsFree t₀ δ:=hδf 0
  have hδ₁ : c.IsFree t₁ δ:=hδf 1
  have hδ₂ : c.IsFree t₂ δ:=hδf 2
  have hδ : InA c a b δ:=Or.inl hδa
  have produce (z' t' : V) (hs : Distinct7 a b u z₀ z' t₀ t') (hdt' : G.degree t'≤d)
      (hg : Good c a b u z') (he : c.col z' t'=some ξ)
      (hfree : c.IsFree t' θ) (hδt : c.IsFree t' δ)
      (hn : ¬(c.kempeGraph ξ δ).Reachable t' t₀) :
      ∃ c' : PEC G (Fin G.maxDegree),∃ z' t' : V,
        G.degree t'≤d ∧ Distinct7 a b u z₀ z' t₀ t' ∧
        ∃ α β₁ β₂ γ₁ γ₂,IsFork c' a b u z₀ z' t₀ t' α β₁ β₂ γ₁ γ₂ := by
    let c':=c.kempeSwap ξ δ t'
    have hw : c.IsFree t' ξ ∨ c.IsFree t' δ:=Or.inr hδt
    have hroot' := rootedAdmissible_kempeSwap hG hroot hξ hδ hw hs.at₂.symm hs.bt₂.symm
    have hgood₀' := good_kempeSwap hG hroot.1 hξ hδ hw hs.at₂.symm hs.bt₂.symm hgood₀
    have hgood' := good_kempeSwap hG hroot.1 hξ hδ hw hs.at₂.symm hs.bt₂.symm hg
    have hθξ : θ≠ξ := by
      intro hh
      subst θ
      exact hfree z' (by rw [c.col_symm];exact he)
    have hθδ : θ≠δ := by
      intro hh
      subst θ
      exact hδ₀ z₀ (by rw [c.col_symm];exact he₀)
    have he₀' : c'.col z₀ t₀=some θ := by
      rw [c'.col_symm]
      change (c.kempeSwap ξ δ t').col t₀ z₀=some θ
      rw [kempeSwap_col,kempeSwapFun_of_not_reachable c ξ δ hn z₀,c.col_symm]
      exact he₀
    have he' : c'.col z' t'=some δ := by
      rw [c'.col_symm]
      change (c.kempeSwap ξ δ t').col t' z'=some δ
      rw [kempeSwap_col,kempeSwapFun_of_reachable c ξ δ (SimpleGraph.Reachable.refl _) z',c.col_symm,he]
      simp
    have hfree' : c'.IsFree t' θ :=
      (kempeSwap_isFree_of_ne c ξ δ t' t' hθξ hθδ).mpr hfree
    have hδ₀' : c'.IsFree t₀ δ := (isFree_kempeSwap_of_not_reachable c ξ δ hn δ).mpr hδ₀
    have hθ' : InA c' a b θ :=
      (inA_kempeSwap_keeps hG hroot.1 hξ hδ hw hs.at₂.symm hs.bt₂.symm θ).mpr hθ
    have hδ' : InA c' a b δ :=
      (inA_kempeSwap_keeps hG hroot.1 hξ hδ hw hs.at₂.symm hs.bt₂.symm δ).mpr hδ
    obtain ⟨hcm',α,hbu',hα'⟩:=hroot'
    obtain ⟨β₁,hu₀,hβ₁⟩:=hgood₀'
    obtain ⟨β₂,hu',hβ₂⟩:=hgood'
    exact ⟨c',z',t',hdt',hs,α,β₁,β₂,θ,δ,
      ⟨hcm',hbu',hu₀,hu',he₀',he',hα',hβ₁,hβ₂,hθ',hδ',hfree',hδ₀'⟩⟩
  by_cases hr : (c.kempeGraph ξ δ).Reachable t₁ t₀
  · have hn : ¬(c.kempeGraph ξ δ).Reachable t₂ t₀ := by
      intro hh
      exact not_three_linked c hseven₁.t₁t₂ hseven₂.t₁t₂ ht₁₂
        (Or.inr hδ₀) (Or.inr hδ₁) (Or.inr hδ₂) hr.symm hh.symm
    exact produce z₂ t₂ hseven₂ hdt₂ hgood₂ he₂ hfree₂ hδ₂ hn
  · exact produce z₁ t₁ hseven₁ hdt₁ hgood₁ he₁ hfree₁ hδ₁ hr

/-- Cao--Chen Claim 5.4 in full: a constructed family of d+2 good arms
produces an actual recolouring and an actual forbidden fork. The mutual
missing-colour conditions are proved by Kempe changes, not assumed. -/
theorem exists_fork_of_good_anchor_family (hcrit : IsDeltaCritical G)
    (c : PEC G (Fin G.maxDegree)) (a b u : V) (d : ℕ) (hd : 2≤d)
    (hroot : RootedAdmissible c a b u) (hda : G.degree a≤d)
    (hdelta : (d+1)*(d+3)≤G.maxDegree)
    (z t : Fin (d+2) → V) (hz : Function.Injective z) (ht : Function.Injective t)
    (hconfig : ∀ i,z i∈goodNeighbours c a b u ∧ t i∈goodSecondNeighbours c a b u ∧
      G.degree (t i)≤d ∧ Good c a b (z i) (t i)) :
    ∃ c' : PEC G (Fin G.maxDegree),∃ z' t' : V,
      G.degree (t 0)≤d ∧ G.degree t'≤d ∧ Distinct7 a b u (z 0) z' (t 0) t' ∧
      ∃ α β₁ β₂ γ₁ γ₂,IsFork c' a b u (z 0) z' (t 0) t' α β₁ β₂ γ₁ γ₂ := by
  have htwod : 2*d≤G.maxDegree := by nlinarith only [hdelta,hd]
  have hseven := selected_arms_distinct7 hcrit hroot d hda htwod z t hz ht hconfig
  have hta (i : Fin (d+2)) : t i≠a := by
    have hn:=(mem_sdiff.mp (hconfig i).2.1).2
    intro he
    exact hn (mem_insert.mpr (Or.inl he))
  have htb (i : Fin (d+2)) : t i≠b := by
    have hn:=(mem_sdiff.mp (hconfig i).2.1).2
    intro he
    apply hn
    rw [he]
    obtain ⟨α,hbu,_⟩:=hroot.2
    exact mem_insert_of_mem (mem_insert_of_mem ((mem_neighborFinset G u b).mpr (c.col_adj hbu).symm))
  have hdt (i : Fin (d+2)) : G.degree (t i)≤d := (hconfig i).2.2.1
  have hgoodU (i : Fin (d+2)) : Good c a b u (z i) := (mem_filter.mp (hconfig i).1).2.2
  have hgoodE (i : Fin (d+2)) : Good c a b (z i) (t i) := (hconfig i).2.2.2
  obtain ⟨c₁,hroot₁,hgoodU₁,hgoodE₁,θ,I,hfirst,hθ,hI,hnotzero,hfree⟩:=
    exists_many_leaves_missing_first_colour hcrit.2.1 c a b u d hroot hda hdelta z t ht hta htb hdt hgoodU hgoodE
  choose γ hγcol hγA using hgoodE₁
  by_cases hdone : ∃ i∈I,c₁.IsFree (t 0) (γ i)
  · obtain ⟨i,hi,hcross⟩:=hdone
    have hi0 : i≠0 := by intro he;subst i;exact hnotzero hi
    have hs:=hseven 0 i hi0.symm
    obtain ⟨hcm₁,α,hbu₁,hα₁⟩:=hroot₁
    obtain ⟨β₁,hu₀,hβ₁⟩:=hgoodU₁ 0
    obtain ⟨β₂,huᵢ,hβ₂⟩:=hgoodU₁ i
    exact ⟨c₁,z i,t i,hdt 0,hdt i,hs,α,β₁,β₂,θ,γ i,
      ⟨hcm₁,hbu₁,hu₀,huᵢ,hfirst,hγcol i,hα₁,hβ₁,hβ₂,hθ,hγA i,hfree i hi,hcross⟩⟩
  · let P:=((univ : Finset (Fin G.maxDegree))\missing c₁ (t 0)).erase θ
    have hθpresent : θ∈(univ : Finset (Fin G.maxDegree))\missing c₁ (t 0) := by
      apply mem_sdiff.mpr
      refine ⟨mem_univ θ,?_⟩
      intro hh
      exact (mem_missing.mp hh) (z 0) (by rw [c₁.col_symm];exact hfirst)
    have hPcard : P.card≤d-1 := by
      have hp:=CommonMissingColour.present_colour_card G.maxDegree c₁ (t 0)
      have he:=card_erase_add_one hθpresent
      have hc : (colNbrs c₁ (t 0)).card≤G.degree (t 0) :=
        (card_le_card (filter_subset (fun v => c₁.col (t 0) v≠none) (G.neighborFinset (t 0)))).trans_eq
          (card_neighborFinset_eq_degree G (t 0))
      change P.card+1=((univ : Finset (Fin G.maxDegree))\missing c₁ (t 0)).card at he
      have ht₀:=hdt 0
      omega
    have hmap : Set.MapsTo γ (I:Set (Fin (d+2))) (P:Set (Fin G.maxDegree)) := by
      intro i hi
      have hnotfree : ¬c₁.IsFree (t 0) (γ i) := by
        intro hh
        exact hdone ⟨i,hi,hh⟩
      have hne : γ i≠θ := by
        intro he
        have hh:=hfree i hi
        rw [←he] at hh
        exact hh (z i) (by rw [c₁.col_symm];exact hγcol i)
      apply mem_erase.mpr
      refine ⟨hne,mem_sdiff.mpr ⟨mem_univ _,?_⟩⟩
      intro hh
      exact hnotfree (mem_missing.mp hh)
    have hcard : P.card<I.card := by omega
    obtain ⟨i,hi,j,hj,hij,hcolour⟩:=exists_ne_map_eq_of_card_lt_of_maps_to hcard hmap
    have hi0 : i≠0 := by intro he;subst i;exact hnotzero hi
    have hj0 : j≠0 := by intro he;subst j;exact hnotzero hj
    have hjcol : c₁.col (z j) (t j)=some (γ i) := by simpa only [hcolour] using hγcol j
    obtain ⟨c',z',t',hdt',hs,hfork⟩:=fork_of_repeated_leaf_colour hcrit.2.1 c₁ a b u (z 0) (z i) (z j) (t 0) (t i) (t j) d
      hroot₁ (hseven 0 i hi0.symm) (hseven 0 j hj0.symm) (fun he => hij (ht he))
      hda (hdt 0) (hdt i) (hdt j) (by nlinarith only [hdelta])
      (hgoodU₁ 0) (hgoodU₁ i) (hgoodU₁ j) θ (γ i) hfirst hθ
      (hγcol i) hjcol (hγA i) (hfree i hi) (hfree j hj)
    exact ⟨c',z',t',hdt 0,hdt',hs,hfork⟩

end OverfullWork.CaoChenForkAssembly
