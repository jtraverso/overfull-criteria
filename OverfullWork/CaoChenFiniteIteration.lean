module

public import OverfullWork.CaoChenRootPaletteNormalization
public import OverfullWork.CaoChenFinitePaletteProgress
public import OverfullWork.CaoChenALowLeafProgress
public import OverfullWork.CaoChenTerminalAssembly
public import OverfullWork.CaoChenFiniteRoleInvariant
public import OverfullWork.CaoChenCandidateSelection
public import OverfullWork.CaoChenALowLeafPreparationLocated
public import OverfullWork.CaoChenUniformPaletteBudgets

@[expose] public section


/-! # Finite selected-palette progress with a decreasing overlap margin

The state tracks the root palette and a fixed protected family. The
special-spine condition is represented by membership in S; its large-A
alternative follows from the same finite role bound as the selected palette.
-/
namespace OverfullWork.CaoChenFiniteIteration
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenFinitePaletteProgress
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 6000000

def margin (M k j : ℕ) : ℕ := M+2*(k-j)

/-- An actual intermediate colouring and selected palette. Neither a
progress step nor a terminal recolouring is included as a premise. -/
structure State (c₀ c : PEC G (Fin G.maxDegree)) (q : ℝ) (x y u : V)
    (α : Fin G.maxDegree) (T₀ T I F : Finset (Fin G.maxDegree)) (k M j : ℕ) : Prop where
  cm : IsColMinus c x y
  rootRow : ∀v,c.col x v=c₀.col x v
  protectedColours : ∀a b γ,γ∈F → (c.col a b=some γ↔c₀.col a b=some γ)
  protectedMembership : ∀γ∈F,γ∈T↔γ∈T₀
  selected : T⊆badColours c q u∩paletteS c q x y
  card : T.card=3*k
  score : j≤(T∩missing c x).card
  special : α∈paletteS c q x y
  large : ∀γ∈insert α T,γ∉I → γ∈paletteA c q x y →
    ∀v,c.col y v=some γ → margin M k j<(missing c v∩missing c x).card

theorem State.root_missing_eq {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ}
    {x y u : V} {α : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)}
    {k M j : ℕ} (hs : State c₀ c q x y u α T₀ T I F k M j) :
    missing c x=missing c₀ x := by
  ext γ
  simp only [mem_missing,IsFree,hs.rootRow]

/-- The weaker B1 alternative is a consequence of the tracked S-role and
the large-root-overlap invariant, rather than an independent oracle. -/
theorem State.spine_role {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ}
    {x y z u : V} {α : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)}
    {k M j : ℕ} (hs : State c₀ c q x y u α T₀ T I F k M j)
    (hxz : c₀.col x z=some α) (hαI : α∉I) :
    CaoChenSecondarySpineNormalization.SpineRole c q x y α (margin M k j) := by
  have hxz' : c.col x z=some α := by rw [hs.rootRow];exact hxz
  have hnot : ¬c.IsFree x α := fun h => h z hxz'
  have hcases : α∈paletteA c q x y ∨ c.IsFree x α ∨ c.IsFree y α := by
    simpa only [paletteS,mem_union,mem_missing,or_assoc] using hs.special
  rcases hcases with hA|hX|hY
  · obtain ⟨_,v,hyv,hvlow⟩:=(mem_paletteA c q x y α).mp hA
    exact Or.inr ⟨v,hyv,hvlow,hs.large α (mem_insert_self _ _) hαI hA v hyv⟩
  · exact False.elim (hnot hX)
  · exact Or.inl hY

omit [DecidableEq V] in
/-- Exact colour-class protection preserves all missing-colour facts in
the protected family, not just already coloured edges. -/
theorem State.protected_free_iff {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ}
    {x y u : V} {α : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)}
    {k M j : ℕ} (hs : State c₀ c q x y u α T₀ T I F k M j)
    {γ : Fin G.maxDegree} (hγ : γ∈F) (v : V) :
    c.IsFree v γ↔c₀.IsFree v γ := by
  constructor
  · intro hf w hw
    exact hf w ((hs.protectedColours v w γ hγ).mpr hw)
  · intro hf w hw
    exact hf w ((hs.protectedColours v w γ hγ).mp hw)

theorem State.protected_present_right {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ}
    {x y u : V} {α : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)}
    {k M j : ℕ} (hs : State c₀ c q x y u α T₀ T I F k M j)
    (hF : ∀γ∈F,γ∈presentColours c₀ y) : ∀γ∈F,γ∈presentColours c y := by
  intro γ hγ
  exact (mem_presentColours c y γ).mpr
    (fun h => (mem_presentColours c₀ y γ).mp (hF γ hγ) ((hs.protected_free_iff hγ y).mp h))

/-- Choosing the actual small-root-overlap colours as I proves the initial
large-role invariant. This lemma constructs the state from concrete palettes. -/
theorem initial_state (c : PEC G (Fin G.maxDegree)) {x y u : V}
    (hcm : IsColMinus c x y) (q : ℝ) (α : Fin G.maxDegree)
    (T F : Finset (Fin G.maxDegree)) (k M : ℕ)
    (hT : T⊆badColours c q u∩paletteS c q x y) (hcard : T.card=3*k)
    (hα : c.IsFree y α) :
    let I:=CaoChenSecondarySpineNormalization.smallRootOverlapColours c q x y
      (insert α T) (margin M k 0)
    State c c q x y u α T T I F k M 0 := by
  dsimp only
  refine ⟨hcm,fun _ => rfl,fun _ _ _ _ => Iff.rfl,fun _ _ => Iff.rfl,
    hT,hcard,Nat.zero_le _,?_,?_⟩
  · exact mem_union.mpr (Or.inr (mem_missing.mpr hα))
  · intro γ hγ hnot hA v hyv
    by_contra hn
    exact hnot (mem_filter.mpr ⟨mem_inter.mpr ⟨hγ,hA⟩,v,hyv,by omega⟩)

omit [DecidableEq V] in
private theorem advance_state {c₀ c d : PEC G (Fin G.maxDegree)} {q : ℝ}
    {x y u : V} {α : Fin G.maxDegree} {T₀ T T' I F : Finset (Fin G.maxDegree)}
    {k M j loss : ℕ} (hs : State c₀ c q x y u α T₀ T I F k M j)
    (hp : Progress c d q x y u T T' F loss)
    (hspecial : α∈paletteS d q x y)
    (hlarge : CaoChenFiniteRoleInvariant.LargeRoles d q x y (insert α T') I (margin M k (j+1))) :
    State c₀ d q x y u α T₀ T' I F k M (j+1) := by
  refine ⟨hp.cm,fun v => (hp.rootRow v).trans (hs.rootRow v),?_,?_,hp.selected,
    hp.card.trans hs.card,?_,hspecial,hlarge⟩
  · intro a b γ hγ
    exact (hp.protectedColours a b γ hγ).trans (hs.protectedColours a b γ hγ)
  · intro γ hγ
    exact (hp.protectedMembership γ hγ).trans (hs.protectedMembership γ hγ)
  · have h0:=hs.score
    have h1:=hp.gain
    omega

/-- Secondary normalization is an actual zero-score transition of the
finite state; its primary-profile inclusion proves the entire large-role
invariant at the unchanged margin. -/
theorem State.after_secondary {c₀ c d : PEC G (Fin G.maxDegree)} {q : ℝ}
    {x y z u : V} {α β : Fin G.maxDegree} {T₀ T I F Tau : Finset (Fin G.maxDegree)}
    {k M j : ℕ} (hs : State c₀ c q x y u α T₀ T I F k M j)
    (hd : CaoChenCandidateSelection.SecondaryCandidate c d q x y z u α β T F Tau k (margin M k j)) :
    State c₀ d q x y u α T₀ T I F k M j := by
  have hFsub : F⊆CaoChenCandidateSelection.protectedFamily α T F :=
    fun γ hγ => mem_insert_of_mem (mem_union_right T hγ)
  have hCsub : insert α T⊆CaoChenCandidateSelection.protectedFamily α T F := by
    intro γ hγ
    rcases mem_insert.mp hγ with rfl|hh
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_union_left F hh)
  refine ⟨hd.normalization.cm,fun v => (hd.normalization.rootRow v).trans (hs.rootRow v),
    ?_,hs.protectedMembership,hd.selected,hs.card,?_,?_,?_⟩
  · intro a b γ hγ
    exact (hd.normalization.protectedColours a b γ (hFsub hγ)).trans (hs.protectedColours a b γ hγ)
  · rw [hd.score]
    exact hs.score
  · exact (CaoChenSecondarySpineNormalization.S_role_iff hd.normalization q α
      (hCsub (mem_insert_self _ _))).mpr hs.special
  · intro γ hγ hγI hγA v hyv
    have hγA₀ : γ∈paletteA c q x y :=
      (CaoChenSecondarySpineNormalization.A_role_iff hd.normalization q γ (hCsub hγ)).mp hγA
    have hyv₀ : c.col y v=some γ :=
      (hd.normalization.protectedColours y v γ (hCsub hγ)).mp hyv
    have hold:=hs.large γ hγ hγI hγA₀ v hyv₀
    by_contra hn
    have hsmall : γ∈CaoChenSecondarySpineNormalization.smallRootOverlapColours d q x y
        (insert α T) (margin M k j) :=
      mem_filter.mpr ⟨mem_inter.mpr ⟨hγ,hγA⟩,v,hyv,by omega⟩
    obtain ⟨_,w,hyw,hw⟩:=mem_filter.mp (hd.primaryColours hsmall)
    have hvw : v=w:=c.col_proper hyv₀ hyw
    rw [←hvw] at hw
    omega

/-- A concrete missing-y gain advances the finite state and spends only
one of the two root-profile units available at each iteration. -/
theorem State.after_literal_gain (hG : IsClassTwo G)
    {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ} {x y u : V}
    {α κ η : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)} {k M j : ℕ}
    (hs : State c₀ c q x y u α T₀ T I F k M j) (hj : j<k)
    (hκ : c.IsFree x κ) (hη : c.IsFree y η)
    (hp : Progress c (c.kempeSwap κ η u) q x y u T (T.image (Equiv.swap κ η)) F 1) :
    State c₀ (c.kempeSwap κ η u) q x y u α T₀ (T.image (Equiv.swap κ η)) I F k M (j+1) := by
  obtain ⟨_,_,hS,_⟩:=CaoChenFiniteRoleInvariant.kempe_gain_preserves_endpoint_palettes
    hG hs.cm q κ η u hκ hη hp.rootRow
  have hlarge:=CaoChenFiniteRoleInvariant.largeRoles_after_kempe_gain hG hs.cm q κ η u
    hκ hη hp.rootRow α T I (margin M k j) (margin M k (j+1)) hs.large
    (by dsimp [margin];omega)
  exact advance_state hs hp (hS ▸ hs.special) hlarge

/-- The complete missing-at-spine branch advances the finite state. Both
the direct branch and the A-colour preparation use actual recolourings. -/
theorem State.gain_from_missing_candidate (hG : IsClassTwo G)
    {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ} {x y u : V}
    {α η : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)} {k M j : ℕ}
    (hs : State c₀ c q x y u α T₀ T I F k M j) (hj : j<k)
    (hscore : (T∩missing c x).card<k) (hIF : I⊆F)
    (hroom : F.card+k+2≤M) (hF : ∀γ∈F,γ∈presentColours c₀ y)
    (hux : u≠x) (huy : u≠y)
    (hηT : η∈T) (hηX : η∉missing c x) (hηF : η∉F) (hηu : c.IsFree u η)
    (hbudget : F.card+T.card<(missing c x).card) :
    ∃d T',State c₀ d q x y u α T₀ T' I F k M (j+1) := by
  by_cases hηy : c.IsFree y η
  · obtain ⟨κ,hκ,hκF,hκT⟩:=exists_root_auxiliary c x F T hbudget
    have hp:=gain_of_two_missing hG hs.cm hux huy q T F hs.selected hκ hηy hηu
      hηT hκT hκF hηF
    exact ⟨c.kempeSwap κ η u,T.image (Equiv.swap κ η),hs.after_literal_gain hG hj hκ hηy hp⟩
  · have hηS : η∈paletteS c q x y := (mem_inter.mp (hs.selected hηT)).2
    have hcases : η∈paletteA c q x y ∨ c.IsFree x η ∨ c.IsFree y η := by
      simpa only [paletteS,mem_union,mem_missing,or_assoc] using hηS
    have hηA : η∈paletteA c q x y := hcases.resolve_right
      (fun h => h.elim (fun hf => hηX (mem_missing.mpr hf)) hηy)
    have hηI : η∉I := fun h => hηF (hIF h)
    have hlarge : ∀w,c.col y w=some η →
        F.card+(T∩missing c x).card<(missing c w∩missing c x).card := by
      intro w hyw
      have hh:=hs.large η (mem_insert_of_mem hηT) hηI hηA w hyw
      dsimp [margin] at hh
      omega
    obtain ⟨w,θ,δ,c₁,T₁,κ,hprep,hκ,hκF,hκT,hp⟩:=exists_A_missing_candidate_gain hG hs.cm
      hux huy q T F hs.selected hηA hηu hηT hηF (hs.protected_present_right hF) hlarge hbudget
    have hgain:=gain_of_two_missing hG hprep.full.cm hux huy q T₁ F hprep.selected
      hκ hprep.full.etaMissing hprep.candidateMissing hprep.candidate hκT hκF hηF
    let m':=margin M k (j+1)
    have hmid:=CaoChenFiniteRoleInvariant.largeRoles_after_full_switch hG hs.cm q η θ δ
      hηA hprep.oldColour hprep.thetaMissing hprep.deltaRoot hprep.full hprep.protectedSwitch
      α T T₁ I (margin M k j) (m'+1) hηT hηI hprep.selectedEq hs.large
      (by dsimp [m',margin];omega)
    have hlast:=CaoChenFiniteRoleInvariant.largeRoles_after_kempe_gain hG hprep.full.cm q κ η u
      hκ hprep.full.etaMissing hgain.rootRow α T₁ I (m'+1) m' hmid (by omega)
    obtain ⟨_,_,hS,_⟩:=CaoChenFiniteRoleInvariant.kempe_gain_preserves_endpoint_palettes
      hG hprep.full.cm q κ η u hκ hprep.full.etaMissing hgain.rootRow
    have hspecial : α∈paletteS (c₁.kempeSwap κ η u) q x y := by
      rw [hS,hprep.full.palette_eq]
      exact hs.special
    exact ⟨c₁.kempeSwap κ η u,T₁.image (Equiv.swap κ η),advance_state hs hp hspecial hlast⟩

/-- A real low-leaf candidate also advances the full finite invariant.
The common leaf colour is protected through the A-preparation and used
by the final literal gain. -/
theorem State.gain_from_leaf_candidate (hG : IsClassTwo G)
    {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ} {x y u t : V}
    {α η κ : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)} {k M j : ℕ}
    (hs : State c₀ c q x y u α T₀ T I F k M j) (hj : j<k)
    (hscore : (T∩missing c x).card<k) (hIF : I⊆F)
    (hroom : F.card+k+2≤M) (hF : ∀γ∈F,γ∈presentColours c₀ y)
    (huy : u≠y) (htx : t≠x)
    (hηT : η∈T) (hηX : η∉missing c x) (hηF : η∉F)
    (hut : c.col u t=some η) (hκx : c.IsFree x κ) (hκt : c.IsFree t κ)
    (hκF : κ∉F) (hκT : κ∉T) :
    ∃d T',State c₀ d q x y u α T₀ T' I F k M (j+1) := by
  by_cases hηy : c.IsFree y η
  · have hp:=CaoChenLowLeafProgress.gain_of_low_leaf_common_root hG hs.cm htx q T F hs.selected
      hκx hηy hut hκt hηT hκT hκF hηF
    exact ⟨c.kempeSwap κ η u,T.image (Equiv.swap κ η),hs.after_literal_gain hG hj hκx hηy hp⟩
  · have hηS : η∈paletteS c q x y := (mem_inter.mp (hs.selected hηT)).2
    have hcases : η∈paletteA c q x y ∨ c.IsFree x η ∨ c.IsFree y η := by
      simpa only [paletteS,mem_union,mem_missing,or_assoc] using hηS
    have hηA : η∈paletteA c q x y := hcases.resolve_right
      (fun h => h.elim (fun hf => hηX (mem_missing.mpr hf)) hηy)
    have hηI : η∉I := fun h => hηF (hIF h)
    obtain ⟨_,w,hyw,_⟩:=(mem_paletteA c q x y η).mp hηA
    have hlarge : (insert κ F).card+(T∩missing c x).card<
        (missing c w∩missing c x).card := by
      have hh:=hs.large η (mem_insert_of_mem hηT) hηI hηA w hyw
      have hc:=card_insert_le κ F
      dsimp [margin] at hh
      omega
    obtain ⟨θ,δ,c₁,T₁,hprep,hTeq⟩:=
      CaoChenALowLeafPreparationLocated.exists_A_low_leaf_preparation_located hG hs.cm huy
        q T F hs.selected hηA hηT hηF (hs.protected_present_right hF) hut hyw
        hκx hκt hκF hκT hlarge
    have hg:=CaoChenLowLeafProgress.gain_of_low_leaf_common_root hG hprep.full.cm htx q T₁ F
      hprep.selected hprep.leafMissingRoot hprep.full.etaMissing hprep.candidateEdge
      hprep.leafMissingLeaf hprep.candidate hprep.leafNotSelected hκF hηF
    have hp : Progress c (c₁.kempeSwap κ η u) q x y u T (T₁.image (Equiv.swap κ η)) F 2 := by
      refine ⟨hg.cm,fun v => (hg.rootRow v).trans (hprep.full.leftRow v),?_,?_,hg.selected,
        hg.card.trans hprep.card,?_,?_⟩
      · intro a b γ hγ
        exact (hg.protectedColours a b γ hγ).trans
          (hprep.protectedColours a b γ (mem_insert_of_mem hγ))
      · intro γ hγ
        exact (hg.protectedMembership γ hγ).trans
          (hprep.protectedMembership γ (mem_insert_of_mem hγ))
      · have h0:=hprep.score
        have h1:=hg.gain
        omega
      · intro v
        have h0:=hprep.rootDrop v
        have h1:=hg.rootDrop v
        omega
    let m':=margin M k (j+1)
    have hmid:=CaoChenFiniteRoleInvariant.largeRoles_after_full_switch hG hs.cm q η θ δ
      hηA hyw hprep.thetaMissing hprep.normMissingRoot hprep.full hprep.protectedSwitch
      α T T₁ I (margin M k j) (m'+1) hηT hηI hTeq hs.large
      (by dsimp [m',margin];omega)
    have hlast:=CaoChenFiniteRoleInvariant.largeRoles_after_kempe_gain hG hprep.full.cm q κ η u
      hprep.leafMissingRoot hprep.full.etaMissing hg.rootRow α T₁ I (m'+1) m' hmid (by omega)
    obtain ⟨_,_,hS,_⟩:=CaoChenFiniteRoleInvariant.kempe_gain_preserves_endpoint_palettes hG
      hprep.full.cm q κ η u hprep.leafMissingRoot hprep.full.etaMissing hg.rootRow
    have hspecial : α∈paletteS (c₁.kempeSwap κ η u) q x y := by
      rw [hS,hprep.full.palette_eq]
      exact hs.special
    exact ⟨c₁.kempeSwap κ η u,T₁.image (Equiv.swap κ η),advance_state hs hp hspecial hlast⟩

/-- One complete effective finite-progress step. A single explicit maximum-
degree cutoff pays for the actual secondary normalization when needed.
There is no one-step or normalization oracle among the assumptions. -/
theorem State.step (hG : IsClassTwo G)
    {c₀ c : PEC G (Fin G.maxDegree)} {x y z u : V} {α β : Fin G.maxDegree}
    {T₀ T I F : Finset (Fin G.maxDegree)} {k j : ℕ}
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hs : State c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y u α T₀ T I F k (2*k+5) j)
    (hj : j<k) (hscore : (T∩missing c x).card<k)
    (hIF : I⊆F) (hFcard : F.card≤k+2) (hTF : (T₀∩F).card≤k)
    (hF : ∀γ∈F,γ∈presentColours c₀ y)
    (hβF : β∈F) (hβT : β∉T₀) (hxu : c₀.col x u=some β) (hxz : c₀.col x z=some α)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hk : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (CaoChenUniformPaletteBudgets.cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ)) :
    ∃d T',State c₀ d ((1-ε)*(G.maxDegree:ℝ)) x y u α T₀ T' I F k (2*k+5) (j+1) := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  have hxu' : c.col x u=some β := by rw [hs.rootRow];exact hxu
  have hxz' : c.col x z=some α := by rw [hs.rootRow];exact hxz
  have hux : u≠x := (c.col_adj hxu').ne.symm
  have huy : u≠y := by intro he;rw [he,hs.cm.uncol] at hxu';contradiction
  have hβnot : β∉T := fun h => hβT ((hs.protectedMembership β hβF).mp h)
  have hTFeq : T∩F=T₀∩F := by
    ext γ
    by_cases hγ : γ∈F
    · simp only [mem_inter,hγ,and_true,hs.protectedMembership γ hγ]
    · simp only [mem_inter,hγ,and_false]
  have hprotected : (T∩F).card≤k := by rw [hTFeq];exact hTF
  have hM : margin (2*k+5) k j≤4*k+5 := by dsimp [margin];omega
  obtain ⟨hnum₁,hnum₂⟩:=CaoChenUniformPaletteBudgets.secondary_budgets k
    (margin (2*k+5) k j) hM
  have hnum₁' : 2*k+2+k*(CaoChenCandidateSelection.secondaryBudget k (margin (2*k+5) k j)+1)≤
      CaoChenUniformPaletteBudgets.cutoff k := hnum₁
  have hnum₂' : CaoChenCandidateSelection.secondaryBudget k (margin (2*k+5) k j)+
      (k+1)*(2*k+2)≤CaoChenUniformPaletteBudgets.cutoff k := hnum₂
  have hmissing:=CaoChenUniformPaletteBudgets.missing_root_gt_cutoff hs.cm ε hε hεone k hx hlarge
  have hthreshold : ((2*k+2:ℕ):ℝ)+(k:ℝ)*
      ((CaoChenCandidateSelection.secondaryBudget k (margin (2*k+5) k j)+1:ℕ):ℝ)≤
      ε^2*(G.maxDegree:ℝ) := by
    have hn : ((2*k+2:ℕ):ℝ)+(k:ℝ)*
        ((CaoChenCandidateSelection.secondaryBudget k (margin (2*k+5) k j)+1:ℕ):ℝ)≤
        (CaoChenUniformPaletteBudgets.cutoff k:ℝ) := by exact_mod_cast hnum₁'
    exact hn.trans hlarge
  have hbudget : CaoChenCandidateSelection.secondaryBudget k (margin (2*k+5) k j)+
      (k+1)*(2*k+2)<(missing c x).card := hnum₂'.trans_lt hmissing
  have hrootBudget : F.card+T.card<(missing c x).card := by
    have hb:=hnum₂'
    dsimp [CaoChenCandidateSelection.secondaryBudget] at hb
    have hc:=hs.card
    omega
  obtain ⟨Tau,hTau,_hTauCard,hcases⟩:=CaoChenCandidateSelection.exists_candidate_or_secondary_leaf
    hG c hs.cm hxu' hxz' T F k (margin (2*k+5) k j) ε hε hεone hx hs.selected hs.card
    hscore hprotected hFcard hβnot hk hthreshold hbudget
  rcases hcases with ⟨η,hη,hηu⟩|⟨d,hd⟩
  · obtain ⟨hηT,hηnot⟩:=mem_sdiff.mp (hTau hη)
    have hηX : η∉missing c x:=fun h => hηnot (mem_union.mpr (Or.inl h))
    have hηF : η∉F:=fun h => hηnot (mem_union.mpr (Or.inr h))
    exact hs.gain_from_missing_candidate hG hj hscore hIF (by omega) hF hux huy
      hηT hηX hηF hηu hrootBudget
  · have hsd:=hs.after_secondary hd
    obtain ⟨η,hη,t,hut,htx,_htlow,_htlarge,κ,hκx,hκt,hκF,hκT⟩:=hd.candidate
    obtain ⟨hηT,hηnot⟩:=mem_sdiff.mp (hTau hη)
    have hηF : η∉F:=fun h => hηnot (mem_union.mpr (Or.inr h))
    have hroot : missing d x=missing c x := by
      ext γ
      simp only [mem_missing,IsFree,hd.normalization.rootRow]
    have hηX : η∉missing d x := by
      rw [hroot]
      exact fun h => hηnot (mem_union.mpr (Or.inl h))
    have hscore' : (T∩missing d x).card<k := by rw [hd.score];exact hscore
    exact hsd.gain_from_leaf_candidate hG hj hscore' hIF (by omega) hF huy htx
      hηT hηX hηF hut hκx hκt hκF hκT

omit [DecidableEq V] in
/-- Reaching score k early already gives the terminal state. Raising the
iteration index weakens the large-profile requirement, so no extra
recolouring is needed. -/
theorem State.terminal_of_score {c₀ c : PEC G (Fin G.maxDegree)} {q : ℝ}
    {x y u : V} {α : Fin G.maxDegree} {T₀ T I F : Finset (Fin G.maxDegree)}
    {k M j : ℕ} (hs : State c₀ c q x y u α T₀ T I F k M j)
    (hscore : k≤(T∩missing c x).card) : State c₀ c q x y u α T₀ T I F k M k := by
  refine ⟨hs.cm,hs.rootRow,hs.protectedColours,hs.protectedMembership,hs.selected,
    hs.card,hscore,hs.special,?_⟩
  intro γ hγ hγI hγA v hyv
  have hh:=hs.large γ hγ hγI hγA v hyv
  dsimp [margin] at hh ⊢
  omega

/-- Actual finite iteration reaches k root-missing selected colours.
Every nonterminal round calls the proved effective step above; all
secondary normalizations and switchings are constructed in that proof.
The theorem assumes no step oracle, extremizer, or terminal colouring. -/
theorem exists_terminal_state (hG : IsClassTwo G)
    {c₀ : PEC G (Fin G.maxDegree)} {x y z u : V} {α β : Fin G.maxDegree}
    {T₀ I F : Finset (Fin G.maxDegree)} {k : ℕ}
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hs₀ : State c₀ c₀ ((1-ε)*(G.maxDegree:ℝ)) x y u α T₀ T₀ I F k (2*k+5) 0)
    (hIF : I⊆F) (hFcard : F.card≤k+2) (hTF : (T₀∩F).card≤k)
    (hF : ∀γ∈F,γ∈presentColours c₀ y)
    (hβF : β∈F) (hβT : β∉T₀) (hxu : c₀.col x u=some β) (hxz : c₀.col x z=some α)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hk : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (CaoChenUniformPaletteBudgets.cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ)) :
    ∃c T,State c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y u α T₀ T I F k (2*k+5) k := by
  have run : ∀r : ℕ,∀j : ℕ,j≤k → k-j=r →
      ∀(c : PEC G (Fin G.maxDegree)) (T : Finset (Fin G.maxDegree)),
      State c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y u α T₀ T I F k (2*k+5) j →
      ∃d T',State c₀ d ((1-ε)*(G.maxDegree:ℝ)) x y u α T₀ T' I F k (2*k+5) k := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro j hj hr c T hs
      by_cases hdone : k≤(T∩missing c x).card
      · exact ⟨c,T,hs.terminal_of_score hdone⟩
      · have hscore : (T∩missing c x).card<k := Nat.lt_of_not_ge hdone
        have hjlt : j<k := hs.score.trans_lt hscore
        obtain ⟨d,T',hd⟩:=hs.step hG ε hε hεone hjlt hscore hIF hFcard hTF hF
          hβF hβT hxu hxz hx hk hlarge
        exact ih (k-(j+1)) (by omega) (j+1) (by omega) rfl d T' hd
  exact run k 0 (Nat.zero_le _) (by omega) c₀ T₀ hs₀

end OverfullWork.CaoChenFiniteIteration
