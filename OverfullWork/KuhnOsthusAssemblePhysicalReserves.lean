module

public import OverfullWork.KuhnOsthusWoundChordRounds
public import OverfullWork.KuhnOsthusJointAbsorptionReserve
public import OverfullWork.KuhnOsthusChordRoundScales
public import OverfullWork.KuhnOsthusExceptionalFactorSequence

@[expose] public section


/-! Apply Lemmas 9.7 and 11.2 to the same physical chord and parity
reserves, uniformly in the ordinary residue. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

/-- The winding count is chosen after the cycle density but before
the bounds on the number and sizes of the clusters. -/
theorem exists_kuhn_osthus_absorption_winding_threshold (ρ : ℝ) (hρ : 0 < ρ) (ell g : ℕ) :
    ∃ fMin : ℕ, ∀ f : ℕ, fMin ≤ f →
      300 ≤ f ∧ 4*ell*390*(8*g^2) ≤ f ∧
      (1+26*(ell:ℝ))*(8*(g:ℝ)^2) ≤ (ρ/512)*(f:ℝ) ∧
      (16:ℝ) ≤ (ρ/128)^2*(f:ℝ) := by
  let A := (1+26*(ell:ℝ))*(8*(g:ℝ)^2)
  let B := (ρ/128)^2
  let f₁ := ⌈A/(ρ/512)⌉₊
  let f₂ := ⌈16/B⌉₊
  refine ⟨max (max 300 (4*ell*390*(8*g^2))) (max f₁ f₂),?_⟩
  intro f hf
  have h₁ : (f₁:ℝ) ≤ f := by
    exact_mod_cast (show f₁ ≤ f from (le_max_left _ _).trans ((le_max_right _ _).trans hf))
  have h₂ : (f₂:ℝ) ≤ f := by
    exact_mod_cast (show f₂ ≤ f from (le_max_right _ _).trans ((le_max_right _ _).trans hf))
  refine ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hf),
    (le_max_right _ _).trans ((le_max_left _ _).trans hf),?_,?_⟩
  · have h := (div_le_iff₀ (show 0 < ρ/512 by positivity)).mp ((Nat.le_ceil _).trans h₁)
    simpa only [A,mul_comm (ρ/512) (f:ℝ)] using h
  · have h := (div_le_iff₀ (show 0 < B by dsimp only [B]; positivity)).mp ((Nat.le_ceil _).trans h₂)
    simpa only [B,mul_comm B (f:ℝ)] using h

set_option maxHeartbeats 2600000 in
/-- Number both reserves on the same physical cluster coordinates.
The bank and factors prepare the rounds for every admissible ordinary
residue. The resulting Hamilton pack covers exactly that residue and the
fixed reserve, including the ordinary parity arcs. -/
theorem kuhn_osthus_lemma_11_2_from_physical_reserves (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n f j g q ell m mWalk mStyle r₁ r₂ r₃ r a : ℕ}
      (G PG : Digraph V) (Z : Finset V)
      (hi : n = f*j) (hj : 0 < j) (Y : Fin (f*j) → Finset V)
      (c : ↥Zᶜ → Fin (f*j)) (cParity : ↥Zᶜ → Fin n)
      (l : Fin n → List (Fin n)) (W : Fin ell → Equiv.Perm (Fin n))
      (order : Fin (ell*n) ≃ Fin ell × Fin n)
      (B₀ : Digraph ↥Zᶜ) (Q : Fin (ell*n) × Fin 4 → Finset ↥Zᶜ)
      (M : ∀ i, Fin r₂ → Q i ≃ Q (((finRotate (ell*n)).prodCongr (Equiv.refl (Fin 4))) i))
      (σ ε : ℝ)
      (F : WoundFactorPacking (G \ PG) Z Y hj (q/f) mStyle r₃ σ),
      let s := r₁+r₂+r-(q-1)*r₃
      let A (i : Fin (f*j)) := (univ : Finset ↥Zᶜ).filter (fun v => c v = i)
      let AParity (i : Fin n) := (univ : Finset ↥Zᶜ).filter (fun v => cParity v = i)
      let sub := Function.Embedding.subtype (· ∈ Zᶜ)
      let B := liftDirectedPair sub sub B₀
      let U := liftDirectedPair sub sub
        (successorCellMatchingUnion Q ((finRotate (ell*n)).prodCongr (Equiv.refl (Fin 4))) M)
      let E := ⨆ i, ⨆ j, (F.factors i j).digraph
      let CA := (U ⊔ E) ⊔ B
      let e := (exceptionalCoordinates Z).toEmbedding
      ∀ (P : Fin s → Digraph (↥Zᶜ ⊕ ↥Z)) (L : Fin s → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z)),
      let PC := liftDirectedPair e e (⨆ i, P i)
      let RB := CA ⊔ PC
      802 ≤ g → g ∣ f → 0 < ell → 0 < mWalk → 300 ≤ f → 4*ell*390*(8*g^2) ≤ f →
      f ≤ m → 24*f ≤ 8*g^2*m →
      (1+26*(ell:ℝ))*(8*(g:ℝ)^2) ≤ (ρ/512)*(f:ℝ) →
      (16:ℝ) ≤ (ρ/128)^2*(f:ℝ) →
      m = 4*ell*mWalk → m = (q/f)*mStyle → f ≤ q/f → (q/f)*f = q → q ∣ f*n →
      (∃ b d : ℕ, f*n = b*10 ∧ f*n = d*3*g.choose 2) →
      r₂ = r*(96*ell*g^2*n) → r*(f*n) = q*r₃ → q*r₃ ≤ r₁ → r*n*f^2 ≤ m →
      N ≤ m → 0 ≤ ε → ε ≤ ρ/512 →
      (∀ v, ¬ G.Adj v v) → PG ≤ G → CA ≤ G \ PG →
      (∀ x, let d := if x ∈ Z then a else a+r
        inDegree PG x = d ∧ outDegree PG x = d) →
      (∀ x, let d := if x ∈ Z then q*r₃ else r₁+r₂+r₃
        inDegree CA x = d ∧ outDegree CA x = d) →
      Disjoint U E → Disjoint (U ⊔ E) B →
      (∀ i v, c v = i ↔ v.val ∈ Y i) → (∀ i, Disjoint (Y i) Z) →
      (∀ v, c v = finCongr hi (cParity v)) →
      (∀ i, (A i).card = m) →
      (∀ i, IsSuperregularPair (induced B Zᶜ) ε ρ (A i) (A (finRotate (f*j) i))) →
      (∀ x y, B.Adj x y → ∃ v w : ↥Zᶜ, v.val = x ∧ w.val = y ∧ c w = finRotate (f*j) (c v)) →
      (∀ v, ∃ i, v ∈ Q i) → (∀ i v, v ∈ Q i → c v = finCongr hi (order i.1).2) →
      (∀ i, (Q i).card = mWalk) → (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) →
      (∀ i p z, p ≠ z → ∀ x, M i p x ≠ M i z x) →
      (∀ i, (order (finRotate (ell*n) i)).2 = W (order i).1 (order i).2) →
      (∀ i, (i :: l i).getLast? = some (finRotate n i)) →
      (∀ x y, ((univ : Finset (Fin ell)).filter (fun j => W j x = y)).card =
        elementaryChordMultiplicity (finRotate n) l x y + if finRotate n x = y then
          ell - (∑ z, elementaryChordMultiplicity (finRotate n) l x z) else 0) →
      (∀ i, P i ≤ pullDirectedPair e e (G \ (PG ⊔ CA)) ∧ AbsorbsWindingFactor AParity (P i) (L i)) →
      Pairwise (fun i j => Disjoint (P i) (P j)) →
      (∀ v, let d := match v with | .inl _ => 6*s | .inr _ => 7*s
        inDegree (⨆ i, P i) v = d ∧ outDegree (⨆ i, P i) v = d) →
      ∀ H : Digraph V, H ≤ G \ RB →
        (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) →
        (∀ v : ↥Zᶜ, inDegree (induced H Zᶜ) v = r ∧ outDegree (induced H Zᶜ) v = r) →
        ∃ T : Fin (r*(f*n)+s*7) → Equiv.Perm V, matchingUnion T = H ⊔ RB ∧
          (∀ i, HasSpanningCycle (fun x y => T i x = y)) ∧
          ∀ i j, i ≠ j → ∀ v, T i v ≠ T j v := by
  obtain ⟨N,hN⟩ := kuhn_osthus_joint_absorption_reserve.{u} ρ hρ hρ₁
  refine ⟨N,?_⟩
  intro V _ n f j g q ell m mWalk mStyle r₁ r₂ r₃ r a G PG Z hi hj Y c cParity l W order B₀ Q M σ ε F
    s A AParity sub B U E CA e P L PC RB
    hg hgf hell hWalkPos hF300 hFine hmF hLarge hFoot hScale hm hStyle hRatio hQ hDiv hDivs hBank hChord hQr hSpace
    hNm hε hε₁ hLoop hPG hCA hDegPG hDegCA hUDis hBDis hCoord hOrdinary hSame hCard hPair hSupport
    hQCover hQParent hQSize hQDis hM hStep hEnd hMult hParity hPApart hPDeg
  subst n
  obtain ⟨u,rfl⟩ := hgf
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  let f := g*u
  let k := f*(j+1)
  let p := q/f
  let K := ((8*g^2*m)/f)+2*(ell*(13*((8*g^2*m)/f)))
  have hf : 0 < f := (by decide : 0 < 300).trans_le hF300
  have hu : 0 < u := by
    by_contra! h
    have he : u = 0 := by omega
    simp [f,he] at hf
  have hp : 0 < p := hf.trans_le hRatio
  have hq : 0 < q := (show p*f = q from hQ) ▸ Nat.mul_pos hp hf
  have hAlign : c = cParity := funext (fun v => hSame v)
  have hSameA : A = AParity := by
    funext i
    ext v
    simp only [A,AParity,mem_filter,hAlign]
  have hParity' : ∀ i, AbsorbsWindingFactor A (P i) (L i) := by
    rw [hSameA]
    exact fun i => (hParity i).2
  have hDel : G \ (PG ⊔ CA) = (G \ PG) \ CA := by
    ext x y
    simp only [Digraph.sdiff_adj,Digraph.sup_adj]
    tauto
  have hParityLe (i) : P i ≤ pullDirectedPair e e ((G \ PG) \ CA) := by
    rw [←hDel]
    exact (hParity i).1
  obtain ⟨z,hz⟩ := hDiv
  have hPC : p*z = k := by
    apply Nat.eq_of_mul_eq_mul_left hf
    calc
      f*(p*z) = (p*f)*z := by ring
      _ = f*k := by rw [show p*f = q from hQ,←hz]
  have hR₃ : r₃ = r*z := by
    apply Nat.eq_of_mul_eq_mul_left hq
    calc
      q*r₃ = r*(f*k) := hChord.symm
      _ = q*(r*z) := by rw [hz]; ring
  obtain ⟨b,d,hb,hd⟩ := hDivs
  have hk : 0 < k := Nat.mul_pos hf (by omega)
  have hD : 0 < d := by
    by_contra! h
    have hd0 : d = 0 := by omega
    rw [hd0,zero_mul,zero_mul] at hd
    exact (Nat.mul_pos hf hk).ne' hd
  have hOrdSize : Fintype.card ↥Zᶜ = k*m := by
    let C : Fin k → Finset ↥Zᶜ := A
    have hCover : (univ : Finset (Fin k)).biUnion C = univ := by
      ext v
      simp only [C,A,mem_biUnion,mem_univ,mem_filter,true_and,iff_true]
      exact ⟨c v,rfl⟩
    calc
      Fintype.card ↥Zᶜ = ((univ : Finset (Fin k)).biUnion C).card := by rw [hCover,card_univ]
      _ = ∑ i : Fin k, (C i).card := card_biUnion (fun i _ j _ hij =>
        disjoint_left.mpr (fun v hv hv' => hij (((mem_filter.mp hv).2).symm.trans (mem_filter.mp hv').2)))
      _ = k*m := by simp only [C,hCard,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]
  have hChoose : 0 < g.choose 2 := Nat.choose_pos (by omega)
  have hSize : 3*d ≤ Fintype.card ↥Zᶜ := by
    rw [hOrdSize]
    calc
      3*d = d*3 := by ring
      _ ≤ d*3*g.choose 2 := Nat.le_mul_of_pos_right _ hChoose
      _ = f*k := hd.symm
      _ ≤ k*m := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right k hmF
  have hTouch : mStyle*f ≤ 2*g^2*m := by
    have h : mStyle*f ≤ m := by rw [hStyle,Nat.mul_comm p]; exact Nat.mul_le_mul_left _ hRatio
    exact h.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hSlots : 300 ≤ f*p := hF300.trans (Nat.le_mul_of_pos_right _ hp)
  have hWalkSize : 2 ≤ ell*k := (((by decide : 2 ≤ 300).trans hF300).trans
    (Nat.le_mul_of_pos_right f (Nat.succ_pos j))).trans (Nat.le_mul_of_pos_left _ hell)
  have hBound : (K:ℝ) ≤ (ρ/512)*(m:ℝ) := integer_chord_round_footprint_budget f g ell m ρ hf hFoot
  have hPrepared (H : Digraph V) (hH : H ≤ G \ RB)
      (hSupp : ∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z)
      (hReg : ∀ v : ↥Zᶜ, inDegree (induced H Zᶜ) v = r ∧ outDegree (induced H Zᶜ) v = r) :
      Nonempty (PreparedChordSystems (H ⊔ U ⊔ E) Z c (finRotate k) K (Fin r × Fin (f*k))) := by
    have hHCA : Disjoint H CA := disjoint_iff_inf_le.mpr (fun _ _ h => (hH h.1).2 (Or.inl h.2))
    have hHU := hHCA.mono_right (le_sup_left.trans le_sup_left)
    have hHE := hHCA.mono_right (le_sup_right.trans le_sup_left)
    have hFE (v : V) (hv : v ∉ Z) : ∃ i, v ∈ F.cell i := by
      let v' : ↥Zᶜ := ⟨v,mem_compl.mpr hv⟩
      have h := (hCoord (c v') v').mp rfl
      rw [←F.cover (c v')] at h
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp h
      exact ⟨(i,c v'),hi⟩
    let transform := finCongr (show r₂ = r*(96*ell*g^2*k) from hBank)
    let factorIndex := finCongr hR₃
    let M' i b := M i (transform.symm b)
    let F' i := F.factors (factorIndex.symm i)
    let next := (finRotate (ell*k)).prodCongr (Equiv.refl (Fin 4))
    have hBankSame : successorCellMatchingUnion Q next M' = successorCellMatchingUnion Q next M := by
      ext x y
      constructor
      · rintro ⟨i,b,v,hx,hy⟩
        exact ⟨i,transform.symm b,v,hx,hy⟩
      · rintro ⟨i,b,v,hx,hy⟩
        exact ⟨i,transform b,v,hx,by simpa only [M',Equiv.symm_apply_apply] using hy⟩
    have hU' : liftDirectedPair sub sub (successorCellMatchingUnion Q next M') = U :=
      congrArg (liftDirectedPair sub sub) hBankSame
    have hE' : (⨆ i, ⨆ j, (F' i j).digraph) = E :=
      factorIndex.symm.iSup_comp (g := fun i => ⨆ j, (F.factors i j).digraph)
    have hRounds := prepare_chord_systems_from_wound_factors Z hg hu hWalkPos hell hm hLarge hFine
      hb.symm (hb.symm.trans hd) hD hSize hPC hSlots hWalkSize c order l W Q M' F.cell mStyle hTouch F'
      hQSize hQParent hQDis (fun i b c h => hM i _ _ (transform.symm.injective.ne h)) hQCover hStep hEnd hMult
      (fun i => (F.size i).1) (fun i => (hOrdinary i.2).mono_left (F.size i).2) F.disjoint hFE
      (fun i v hv => (hCoord i.2 v).mpr ((F.size i).2 hv))
      (fun i j h => F.apart (factorIndex.symm.injective.ne h))
    dsimp only at hRounds
    rw [hU',hE'] at hRounds
    exact hRounds H hSupp hReg (fun v h => hLoop v (hH h).1) hHU (disjoint_sup_left.mpr ⟨hHE,hUDis⟩)
  have hRoom : r*(f*k) ≤ r₁+r₂+r+r₃ := by
    rw [hChord]
    exact hQr.trans (by omega)
  exact (hN hk G PG B U E Z c r f q r₁ r₂ r₃ m K a ε P L hPG hCA hParityLe hParity' hPApart hPDeg
    hDegPG hDegCA hBDis hNm hε hε₁ hBound hSpace hScale hq hChord hRoom hCard hPair hSupport hPrepared).2.2.2

end OverfullWork.DirectedRobustExpansion
