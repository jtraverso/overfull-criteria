module

public import OverfullWork.KuhnOsthusExtenderScheme
public import OverfullWork.KuhnOsthusResidualExtender
public import OverfullWork.KuhnOsthusPhysicalExceptionalInterval

@[expose] public section


/-! Transfer the sampled bounds of the extender from pair coordinates
to the physical vertices used by the Hamilton extension. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V W I : Type*} [Fintype V] [Fintype W]

omit [Fintype V] in
private theorem map_pair_filter (a : W ↪ V) (X : Finset V)
    (hX : ∀ x ∈ X, ∃ w, a w = x) (P : V → Prop) :
    ((univ.filter (fun w => a w ∈ X)).filter (fun w => P (a w))).map a = X.filter P := by
  ext x
  simp only [mem_map,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact hw
  · rintro ⟨hx,hp⟩
    obtain ⟨w,rfl⟩ := hX x hx
    exact ⟨w,⟨hx,hp⟩,rfl⟩

/-- Reading each reserve on its actual cluster pair supplies the
physical bounds needed by the residual extender. -/
theorem ExtenderPairBounds.of_coordinates {q : ℕ}
    (G : Digraph (Fin (q+1))) (H R : Digraph V)
    (cluster : V → Fin (q+1)) (label : V → Fin 50) (a : Fin (q+1) → W ↪ V)
    (u : ℕ) (d p η μ ζ b c : ℝ)
    (hOrder : Fintype.card W = 50*u)
    (hCoord : ∀ i x, cluster x = i ↔ ∃ w, a i w = x)
    (hCell : ∀ i j, (univ.filter (fun w => label (a i w) = j)).card = u)
    (hCycle : ∀ i, SparseSuccessorPairBounds
      (pullDirectedPair (a i) (a (finRotate (q+1) i)) R) d η μ ζ)
    (hChord : ∀ i j, G.Adj i j → SparseSuccessorPairBounds
      (pullDirectedPair (a i) (a j) H) p η μ 0)
    (hIn : ∀ i j v, b ≤ (inNeighbours
      (pullDirectedPair (a i) (a (finRotate (q+1) i)) R)
        (univ.filter (fun w => label (a i w) = j)) v:ℝ))
    (hOut : ∀ i j v, b ≤ (outTo
      (pullDirectedPair (a i) (a (finRotate (q+1) i)) R)
        (univ.filter (fun w => label (a (finRotate (q+1) i) w) = j)) v:ℝ))
    (hCG : (d/μ)^2*(50*u) ≤ c) :
    ExtenderPairBounds G H R cluster label u d p η b c := by
  let s := finRotate (q+1)
  let X₀ (i : Fin (q+1)) (X : Finset V) := univ.filter (fun w => a i w ∈ X)
  have hMap (i : Fin (q+1)) (X : Finset V) (hX : ∀ x ∈ X, cluster x = i) :
      (X₀ i X).map (a i) = X := by
    simpa only [filter_true] using
      map_pair_filter (a i) X (fun x hx => (hCoord i x).mp (hX x hx)) (fun _ => True)
  have hSize (i : Fin (q+1)) (X : Finset V) (hX : ∀ x ∈ X, cluster x = i) :
      (X₀ i X).card = X.card := by
    exact (card_map (f := a i)).symm.trans (congrArg Finset.card (hMap i X hX))
  have hCount (i : Fin (q+1)) (j : Fin 50) (P : V → Prop) :
      ((univ.filter (fun w => label (a i w) = j)).filter (fun w => P (a i w))).card =
      ((univ.filter (fun x => cluster x = i ∧ label x = j)).filter P).card := by
    let X := (univ : Finset V).filter (fun x => cluster x = i ∧ label x = j)
    have he : (univ : Finset W).filter (fun w => label (a i w) = j) = X₀ i X := by
      ext w
      have hi : cluster (a i w) = i := (hCoord i _).mpr ⟨w,rfl⟩
      simp only [X,X₀,mem_filter,mem_univ,true_and,hi]
    rw [he,←card_map (f := a i)]
    exact congrArg Finset.card (map_pair_filter (a i) X (fun x hx =>
      (hCoord i x).mp (mem_filter.mp hx).2.1) P)
  have rect (D : Digraph V) (i j : Fin (q+1)) (X Y : Finset V)
      (hX : ∀ x ∈ X, cluster x = i) (hY : ∀ y ∈ Y, cluster y = j)
      (f z : ℝ) (hD : SparseSuccessorPairBounds (pullDirectedPair (a i) (a j) D) f η μ z)
      (hx : η*(50*u) ≤ (X.card:ℝ)) (hy : η*(50*u) ≤ (Y.card:ℝ)) :
      (1-η)*f*(X.card:ℝ)*(Y.card:ℝ) ≤ incidences D X Y := by
    have hOrder' : (Fintype.card W:ℝ) = 50*u := by exact_mod_cast hOrder
    have h := hD.rectangle (X₀ i X) (X₀ j Y)
      (by rwa [hOrder',hSize i X hX]) (by rwa [hOrder',hSize j Y hY])
    rwa [hSize i X hX,hSize j Y hY,incidences_pull_pair,hMap i X hX,hMap j Y hY] at h
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j
    have h := hCount i j (fun _ => True)
    simpa only [filter_true,hCell] using h.symm
  · intro i X Y hX hY hx hy
    exact rect R i (s i) X Y hX hY d ζ (hCycle i) hx hy
  · intro i j hij X Y hX hY hx hy
    exact rect H i j X Y hX hY p 0 (hChord i j hij) hx hy
  · intro i j v hv
    obtain ⟨x,rfl⟩ := (hCoord (s i) v).mp hv
    have h := hIn i j x
    have hc := hCount i j (fun w => R.Adj w (a (s i) x))
    exact h.trans (by exact_mod_cast hc.le)
  · intro i j v hv
    obtain ⟨x,rfl⟩ := (hCoord i v).mp hv
    have h := hOut i j x
    have hc := hCount (s i) j (R.Adj (a i x))
    exact h.trans (by exact_mod_cast hc.le)
  · intro i x y hx hy hxy
    obtain ⟨x,rfl⟩ := (hCoord (s i) x).mp hx
    obtain ⟨y,rfl⟩ := (hCoord (s i) y).mp hy
    have h := (hCycle i).in_codegree x y (fun h => hxy (congrArg (a (s i)) h))
    have hc := map_pair_filter (a i) (univ.filter (fun v => cluster v = i))
      (fun v hv => (hCoord i v).mp (mem_filter.mp hv).2)
      (fun v => R.Adj v (a (s i) x) ∧ R.Adj v (a (s i) y))
    have he : (univ.filter (fun w => a i w ∈
        (univ : Finset V).filter (fun v => cluster v = i))) = univ := by
      ext w
      simp only [mem_filter,mem_univ,true_and]
      exact iff_true_intro ((hCoord i (a i w)).mpr ⟨w,rfl⟩)
    rw [he] at hc
    have hCard := congrArg Finset.card hc
    rw [card_map] at hCard
    have hEq : commonInNeighbours (pullDirectedPair (a i) (a (s i)) R) x y =
        ((univ.filter (fun v => cluster v = i)).filter
          (fun v => R.Adj v (a (s i) x) ∧ R.Adj v (a (s i) y))).card := by
      trans ((univ : Finset W).filter (fun w =>
        R.Adj (a i w) (a (s i) x) ∧ R.Adj (a i w) (a (s i) y))).card
      · unfold commonInNeighbours
        apply congrArg Finset.card
        exact filter_congr_decidable _ _ _
      · convert hCard using 1
        all_goals
          apply congrArg Finset.card
          ext v
          simp only [mem_filter,mem_univ,true_and]
    have hOrder' : (Fintype.card W:ℝ) = 50*u := by exact_mod_cast hOrder
    rw [←hEq]
    rw [hOrder'] at h
    exact h.trans hCG
  · intro i x y hx hy hxy
    obtain ⟨x,rfl⟩ := (hCoord i x).mp hx
    obtain ⟨y,rfl⟩ := (hCoord i y).mp hy
    have h := (hCycle i).out_codegree x y (fun h => hxy (congrArg (a i) h))
    have hc := map_pair_filter (a (s i)) (univ.filter (fun v => cluster v = s i))
      (fun v hv => (hCoord (s i) v).mp (mem_filter.mp hv).2)
      (fun v => R.Adj (a i x) v ∧ R.Adj (a i y) v)
    have he : (univ.filter (fun w => a (s i) w ∈
        (univ : Finset V).filter (fun v => cluster v = s i))) = univ := by
      ext w
      simp only [mem_filter,mem_univ,true_and]
      exact iff_true_intro ((hCoord (s i) (a (s i) w)).mpr ⟨w,rfl⟩)
    rw [he] at hc
    have hCard := congrArg Finset.card hc
    rw [card_map] at hCard
    have hEq : commonInNeighbours (reverseArcs (pullDirectedPair (a i) (a (s i)) R)) x y =
        ((univ.filter (fun v => cluster v = s i)).filter
          (fun v => R.Adj (a i x) v ∧ R.Adj (a i y) v)).card := by
      trans ((univ : Finset W).filter (fun w =>
        R.Adj (a i x) (a (s i) w) ∧ R.Adj (a i y) (a (s i) w))).card
      · unfold commonInNeighbours
        apply congrArg Finset.card
        exact filter_congr_decidable _ _ _
      · convert hCard using 1
        all_goals
          apply congrArg Finset.card
          ext v
          simp only [mem_filter,mem_univ,true_and]
    have hOrder' : (Fintype.card W:ℝ) = 50*u := by exact_mod_cast hOrder
    rw [←hEq]
    rw [hOrder'] at h
    exact h.trans hCG

/-- Sample the two physical reserves of Lemma 8.2 from the same host
and obtain the per-style degree bounds needed in every use of Lemma 8.3.
Uniformity is required of the host style cells before sampling. -/
theorem exists_physical_extender_with_style_degrees
    (d d₀ δ ε ζ η aStyle : ℝ) (q : ℕ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hd₀ : 0 < d₀)
    (hSmall : d₀ ≤ d/4) (hε : 0 < ε) (hδε : δ ≤ ε) (hRel : 4*δ ≤ ε*d)
    (hδd : δ ≤ d/4) (hζ1 : ζ ≤ 1/2) (hη : 0 < η)
    (hCut : 4*η ≤ ε^3*(d₀/((q+1):ℕ))) (hMax : 2*η ≤ d₀/((q+1):ℕ))
    (hCodeg : η ≤ (d₀/((q+1):ℕ))^2) (hMin : 4*η ≤ d₀) :
    ∃ N : ℕ, ∀ {W : Type u_1} [Fintype W] {V : Type u_2} [Fintype V]
      (D : Digraph V) (G : Digraph (Fin (q+1))) (a : Fin (q+1) → W ↪ V)
      (cluster : V → Fin (q+1)) (label : V → Fin 50)
      (densityOf : Fin (q+1) → Fin (q+1) → ℝ) (u : ℕ),
      let s := finRotate (q+1)
      let P i j := pullDirectedPair (a i) (a j) D
      let A i j := univ.filter (fun w => label (a i w) = j)
      N ≤ Fintype.card W → Fintype.card W = 50*u →
      (∀ i x, cluster x = i ↔ ∃ w, a i w = x) →
      (∀ i j, (A i j).card = u) →
      (∀ i j, d ≤ densityOf i j ∧ densityOf i j ≤ 1) →
      (∀ i j, s i = j ∨ G.Adj i j → IsCentredRegular (P i j) δ (densityOf i j)) →
      (∀ i v, (densityOf i (s i)-δ)*(Fintype.card W:ℝ) ≤ inDegree (P i (s i)) v ∧
        (densityOf i (s i)-δ)*(Fintype.card W:ℝ) ≤ outDegree (P i (s i)) v) →
      (∀ i v j, aStyle*densityOf i (s i)*(Fintype.card W:ℝ) ≤ inNeighbours (P i (s i)) (A i j) v ∧
        aStyle*densityOf i (s i)*(Fintype.card W:ℝ) ≤ outTo (P i (s i)) (A (s i) j) v) →
      ∃ H R : Digraph V, Disjoint H R ∧ H ⊔ R ≤ D ∧
        ExtenderPairBounds G H R cluster label u d₀ (d₀/((q+1):ℕ)) ε
          ((aStyle*d₀-η)*(50*u)) ((d₀/(d/2))^2*(50*u)) ∧
        ∀ v, (inDegree (H ⊔ R) v:ℝ) + outDegree (H ⊔ R) v ≤ (8*d₀/d)*(50*u) := by
  obtain ⟨N,hN⟩ := exists_extender_of_cluster_pairs_with_styles.{u_1} (q+1) d d₀ δ ε ζ η aStyle
    (by omega) hd hd1 hd₀ hSmall hε hδε hRel hδd hζ1 hη hCut hMax hCodeg hMin
  refine ⟨N,?_⟩
  intro W _ V _ D G a cluster label densityOf u s P A hn hOrder hCoord hCell hDen hReg hDegree hStyle
  let I := Fin (q+1) × Fin (q+1)
  let a₁ (i : I) := a i.1
  let a₂ (i : I) := a i.2
  let pairs (i : I) := P i.1 i.2
  let cycle : Set I := {i | s i.1 = i.2}
  let reduced : Set I := {i | G.Adj i.1 i.2}
  have hDis (i j : I) (hij : i ≠ j) :
      Disjoint (liftDirectedPair (a₁ i) (a₂ i) (pairs i))
        (liftDirectedPair (a₁ j) (a₂ j) (pairs j)) := by
    apply disjoint_iff_inf_le.mpr
    rintro x y ⟨⟨v,w,hvx,hwy,_⟩,⟨v',w',hvx',hwy',_⟩⟩
    exact hij (Prod.ext
      (((hCoord i.1 x).mpr ⟨v,hvx⟩).symm.trans ((hCoord j.1 x).mpr ⟨v',hvx'⟩))
      (((hCoord i.2 y).mpr ⟨w,hwy⟩).symm.trans ((hCoord j.2 y).mpr ⟨w',hwy'⟩)))
  obtain ⟨C,E,hInactiveC,hInactiveE,hPE1,hPE2,hCE,hSub,hStyled⟩ :=
    hN a₁ a₂ pairs (fun i => densityOf i.1 i.2) cycle reduced
      (fun i => A i.1) (fun i => A i.2) hn (fun i => hDen i.1 i.2) (fun i => hReg i.1 i.2)
      (fun ⟨i,j⟩ hi => by
        have he : s i = j := hi
        subst j
        exact hDegree i)
      (fun ⟨i,j⟩ hi => by
        have he : s i = j := hi
        subst j
        exact hStyle i) hDis
  let R := directedPairUnion a₁ a₂ C
  let H := directedPairUnion a₁ a₂ E
  have hpull (F : I → Digraph W) (i j : Fin (q+1)) :
      pullDirectedPair (a i) (a j) (directedPairUnion a₁ a₂ F) = F (i,j) := by
    ext x y
    constructor
    · rintro ⟨l,v,w,hv,hw,h⟩
      have hl : l = (i,j) := Prod.ext
        (((hCoord l.1 (a i x)).mpr ⟨v,hv⟩).symm.trans ((hCoord i (a i x)).mpr ⟨x,rfl⟩))
        (((hCoord l.2 (a j y)).mpr ⟨w,hw⟩).symm.trans ((hCoord j (a j y)).mpr ⟨y,rfl⟩))
      subst l
      exact (a i).injective hv ▸ (a j).injective hw ▸ h
    · exact fun h => ⟨(i,j),x,y,rfl,rfl,h⟩
  have hD : directedPairUnion a₁ a₂ pairs ≤ D := by
    rintro x y ⟨i,v,w,rfl,rfl,h⟩
    exact h
  have hM : (Fintype.card W:ℝ) = 50*u := by exact_mod_cast hOrder
  refine ⟨H,R,hCE.symm,?_,?_,?_⟩
  · rw [sup_comm]
    exact hSub.trans hD
  · apply ExtenderPairBounds.of_coordinates G H R cluster label a
      u d₀ (d₀/((q+1):ℕ)) ε (d/2) ζ _ _ hOrder hCoord hCell
    · intro i
      rw [hpull]
      exact (hPE1 (i,s i) rfl).1
    · intro i j hij
      rw [hpull]
      exact (hPE2 (i,j) hij).1
    · intro i j v
      rw [hpull,←hM]
      exact (hStyled (i,s i) rfl v j).1
    · intro i j v
      rw [hpull,←hM]
      exact (hStyled (i,s i) rfl v j).2
    · exact le_rfl

  · have hCount (v : V) :
        (univ.filter (fun i => i ∈ cycle ∧ v ∈ Set.range (a₁ i))).card +
          (univ.filter (fun i => i ∈ cycle ∧ v ∈ Set.range (a₂ i))).card ≤ 2 ∧
        (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (a₁ i))).card +
          (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (a₂ i))).card ≤ 2*(q+1) := by
      have hSource {i j : I} (hi : v ∈ Set.range (a₁ i)) (hj : v ∈ Set.range (a₁ j)) :
          i.1 = j.1 := ((hCoord i.1 v).mpr hi).symm.trans ((hCoord j.1 v).mpr hj)
      have hTarget {i j : I} (hi : v ∈ Set.range (a₂ i)) (hj : v ∈ Set.range (a₂ j)) :
          i.2 = j.2 := ((hCoord i.2 v).mpr hi).symm.trans ((hCoord j.2 v).mpr hj)
      have hc₁ : (univ.filter (fun i => i ∈ cycle ∧ v ∈ Set.range (a₁ i))).card ≤ 1 := by
        apply card_le_one.mpr
        intro i hi j hj
        obtain ⟨hci,hri⟩ := (mem_filter.mp hi).2
        obtain ⟨hcj,hrj⟩ := (mem_filter.mp hj).2
        have hf := hSource hri hrj
        exact Prod.ext hf ((show s i.1 = i.2 from hci).symm.trans ((congrArg s hf).trans hcj))
      have hc₂ : (univ.filter (fun i => i ∈ cycle ∧ v ∈ Set.range (a₂ i))).card ≤ 1 := by
        apply card_le_one.mpr
        intro i hi j hj
        obtain ⟨hci,hri⟩ := (mem_filter.mp hi).2
        obtain ⟨hcj,hrj⟩ := (mem_filter.mp hj).2
        have hf := hTarget hri hrj
        exact Prod.ext (s.injective ((show s i.1 = i.2 from hci).trans (hf.trans
          (show s j.1 = j.2 from hcj).symm))) hf
      have hr₁ : (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (a₁ i))).card ≤ q+1 := by
        have hCard : (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (a₁ i))).card ≤
            (univ : Finset (Fin (q+1))).card := by
          apply card_le_card_of_injOn Prod.snd (fun _ _ => mem_univ _) (fun i hi j hj he =>
            Prod.ext (hSource (mem_filter.mp hi).2.2 (mem_filter.mp hj).2.2) he)
        simpa only [card_univ,Fintype.card_fin] using hCard
      have hr₂ : (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (a₂ i))).card ≤ q+1 := by
        have hCard : (univ.filter (fun i => i ∈ reduced ∧ v ∈ Set.range (a₂ i))).card ≤
            (univ : Finset (Fin (q+1))).card := by
          apply card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) (fun i hi j hj he =>
            Prod.ext he (hTarget (mem_filter.mp hi).2.2 (mem_filter.mp hj).2.2))
        simpa only [card_univ,Fintype.card_fin] using hCard
      exact ⟨by omega,by omega⟩
    intro v
    have h := extender_total_degree_bound a₁ a₂ C E cycle reduced (q+1) d d₀
      (by omega) hd hd₀.le hInactiveC hInactiveE
      (fun i hi => (hPE1 i hi).2.1) (fun i hi => (hPE2 i hi).2.1)
      (fun w => by
        convert (hCount w).1 using 3 <;> congr 1 <;> ext x <;> simp only [mem_filter])
      (fun w => by
        convert (hCount w).2 using 3) hCE v
    rw [hM] at h
    simpa only [H,R,sup_comm] using h

/-- Turn one pair of already sampled reserves into an extender valid
through every bounded prefix deletion. In particular the reserves
of Lemma 8.6 can be used without a second sampling step. -/
theorem exists_bounded_path_extension_of_sampled_pairs
    (d d₀ ε ζ' ν τ γ : ℝ) (q : ℕ) (hq : 0 < q)
    (hd : 0 < d) (hd₀ : 0 < d₀) (hε : 0 < ε)
    (hε1 : 5*ε < 1) (hζ' : 0 < ζ') (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hGamma : γ ≤ ζ'*d₀)
    (hScale : 160*(5*ε) ≤ (ζ'*(d/4))^2) (hDiscard : 8*ν ≤ τ*(ζ'*d₀)^2)
    (hνDensity : ν < (1-5*ε)*d₀*(5*ε)) :
    ∃ N : ℕ, ∀ {V : Type u_2} [Fintype V]
      (G : Digraph (Fin q)) (H R : Digraph V)
      (cluster : V → Fin q) (label : V → Fin 50)
      (u e k r g t cap budget maxArcs : ℕ) (b : ℝ),
      N ≤ u → 0 < u →
      ExtenderPairBounds G H R cluster label u d₀ (d₀/(q:ℕ)) ε b ((d₀/(d/2))^2*(50*u)) →
      (∀ i, ¬ G.Adj i i) →
      IsRobustAt G r t → 0 < g → 2*budget+g ≤ r →
      (∀ i, t+2*budget ≤ outDegree G i) → (∀ i, t ≤ inDegree G i) →
      maxArcs * (2*(q/g+3)) < cap*(budget+1) → 100*(cap+2) ≤ 50*u →
      e ≤ u → (2*ε)*(50*u) ≤ (e:ℝ)+1 →
      16 ≤ (ζ'*d₀)^2*(21*u) →
      (k:ℝ) ≤ ε*(d₀/(q:ℕ))*((2*ε)*(50*u)) →
      ζ'*d₀*(50*u)+(k:ℝ) ≤ 21*b →
      HasBoundedPathExtension (H ⊔ R) label maxArcs k := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  let p := d₀/((q+1):ℕ)
  have hp : 0 < p := div_pos hd₀ (by positivity)
  have hp' : p ≤ d₀ := by
    have hq : (1:ℝ) ≤ (q+1 : ℕ) := by exact_mod_cast q.succ_pos
    exact div_le_self hd₀.le hq
  obtain ⟨N,hN⟩ := exists_hamilton_extension_of_residual_extender.{u_2}
    d₀ p (5*ε) (d/4) ζ' ν τ γ ε (2*ε)
    hd₀ hp (by positivity) hε1 (by positivity) hζ' hν hτ hτγ hγ hGamma hScale hDiscard hνDensity
    (by linarith only [hε]) (by linarith only [hε,hε1]) (by linarith only [hε])
  refine ⟨N,?_⟩
  intro V _ G H R cluster label u e k r g t cap budget maxArcs b hn hu hPairs hLoop hRobust hg
    hAvoid hOut hIn hMass hCap he hCutSize hDiagonal hPay hStyles
  have hPayR : (k:ℝ) ≤ ((2*ε)-ε)*d₀*((2*ε)*(50*u)) := by
    have h := mul_le_mul_of_nonneg_left hp' hε.le
    have hh := mul_le_mul_of_nonneg_right h (show (0:ℝ) ≤ (2*ε)*(50*u) by positivity)
    linarith only [hPay,hh]
  have hPayH : (k:ℝ) ≤ ((2*ε)-ε)*p*((2*ε)*(50*u)) := by
    linarith only [hPay]
  have hCodeg' : (d₀/(d/2))^2*(50*u) ≤ (d₀/(d/4))^2*(21*u) := by
    have heq : d₀/(d/4) = 2*(d₀/(d/2)) := by
      field_simp
      norm_num
    rw [heq]
    have h : 0 ≤ (d₀/(d/2))^2*(u:ℝ) := by positivity
    nlinarith only [h]
  exact hN G H R cluster label u e k r g t cap budget maxArcs _ _ hPairs hLoop
    hRobust hg hAvoid hOut hIn hMass hCap hu he (by omega) hCutSize
    (by nlinarith only [mul_nonneg hε.le (Nat.cast_nonneg u : (0:ℝ) ≤ u)])
    hDiagonal hCodeg' hPayR hPayH hStyles

/-- A normalized consistent layout supplies one physical extender
for every round, with the same style labels as the host. The
successor completion uses tolerance `5*ε` and the original
pair error grows to `2*ε` after deletion. -/
theorem exists_bounded_path_extender_of_cluster_pairs
    (d d₀ δ ε ζ η aStyle ζ' ν τ γ : ℝ) (q : ℕ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hd₀ : 0 < d₀)
    (hSmall : d₀ ≤ d/4) (hε : 0 < ε) (hδε : δ ≤ ε) (hRel : 4*δ ≤ ε*d)
    (hδd : δ ≤ d/4) (hζ : ζ ≤ 1/2) (hη : 0 < η)
    (hCut : 4*η ≤ ε^3*(d₀/((q+1):ℕ))) (hMax : 2*η ≤ d₀/((q+1):ℕ))
    (hCodeg : η ≤ (d₀/((q+1):ℕ))^2) (hMin : 4*η ≤ d₀)
    (hε1 : 5*ε < 1) (hζ' : 0 < ζ') (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hGamma : γ ≤ ζ'*d₀)
    (hScale : 160*(5*ε) ≤ (ζ'*(d/4))^2) (hDiscard : 8*ν ≤ τ*(ζ'*d₀)^2)
    (hνDensity : ν < (1-5*ε)*d₀*(5*ε)) :
    ∃ N : ℕ, ∀ {W : Type u_1} [Fintype W] {V : Type u_2} [Fintype V]
      (D : Digraph V) (G : Digraph (Fin (q+1))) (a : Fin (q+1) → W ↪ V)
      (cluster : V → Fin (q+1)) (label : V → Fin 50)
      (densityOf : Fin (q+1) → Fin (q+1) → ℝ) (u e k r g t cap budget maxArcs : ℕ),
      let s := finRotate (q+1)
      let P i j := pullDirectedPair (a i) (a j) D
      let A i j := univ.filter (fun w => label (a i w) = j)
      N ≤ u → 0 < u → Fintype.card W = 50*u →
      (∀ i x, cluster x = i ↔ ∃ w, a i w = x) →
      (∀ i j, (A i j).card = u) →
      (∀ i j, d ≤ densityOf i j ∧ densityOf i j ≤ 1) →
      (∀ i j, s i = j ∨ G.Adj i j → IsCentredRegular (P i j) δ (densityOf i j)) →
      (∀ i v, (densityOf i (s i)-δ)*(Fintype.card W:ℝ) ≤ inDegree (P i (s i)) v ∧
        (densityOf i (s i)-δ)*(Fintype.card W:ℝ) ≤ outDegree (P i (s i)) v) →
      (∀ i v j, aStyle*densityOf i (s i)*(Fintype.card W:ℝ) ≤ inNeighbours (P i (s i)) (A i j) v ∧
        aStyle*densityOf i (s i)*(Fintype.card W:ℝ) ≤ outTo (P i (s i)) (A (s i) j) v) →
      (∀ i, ¬ G.Adj i i) →
      IsRobustAt G r t → 0 < g → 2*budget+g ≤ r →
      (∀ i, t+2*budget ≤ outDegree G i) → (∀ i, t ≤ inDegree G i) →
      maxArcs * (2*((q+1)/g+3)) < cap*(budget+1) → 100*(cap+2) ≤ 50*u →
      e ≤ u → (2*ε)*(50*u) ≤ (e:ℝ)+1 →
      16 ≤ (ζ'*d₀)^2*(21*u) →
      (k:ℝ) ≤ ε*(d₀/((q+1):ℕ))*((2*ε)*(50*u)) →
      ζ'*d₀*(50*u)+(k:ℝ) ≤ 21*((aStyle*d₀-η)*(50*u)) →
      ∃ H R : Digraph V, Disjoint H R ∧ H ⊔ R ≤ D ∧
        HasBoundedPathExtension (H ⊔ R) label maxArcs k ∧
        ∀ v, (inDegree (H ⊔ R) v:ℝ) + outDegree (H ⊔ R) v ≤ (8*d₀/d)*(50*u) := by
  obtain ⟨N₀,hN₀⟩ := exists_physical_extender_with_style_degrees.{u_1,u_2}
    d d₀ δ ε ζ η aStyle q hd hd1 hd₀ hSmall hε hδε hRel hδd hζ hη hCut hMax hCodeg hMin
  obtain ⟨N₁,hN₁⟩ := exists_bounded_path_extension_of_sampled_pairs.{u_2}
    d d₀ ε ζ' ν τ γ (q+1) q.succ_pos hd hd₀ hε hε1 hζ' hν hτ hτγ hγ hGamma hScale hDiscard hνDensity
  refine ⟨max N₀ N₁,?_⟩
  intro W _ V _ D G a cluster label densityOf u e k r g t cap budget maxArcs s P A
    hn hu hOrder hCoord hCell hDen hReg hDeg hStyle hLoop hRobust hg hAvoid hOut hIn hMass hCap
    he hCutSize hDiagonal hPay hStyles
  obtain ⟨H,R,hDis,hSub,hPairs,hDegreeSum⟩ := hN₀ D G a cluster label densityOf u (by omega)
    hOrder hCoord hCell hDen hReg hDeg hStyle
  refine ⟨H,R,hDis,hSub,?_,hDegreeSum⟩
  exact hN₁ G H R cluster label u e k r g t cap budget maxArcs _ (by omega) hu hPairs hLoop
    hRobust hg hAvoid hOut hIn hMass hCap he hCutSize hDiagonal hPay hStyles

end OverfullWork.DirectedRobustExpansion
