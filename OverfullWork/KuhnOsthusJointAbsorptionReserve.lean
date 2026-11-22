module

public import OverfullWork.KuhnOsthusChordAbsorptionLink
public import OverfullWork.KuhnOsthusFinalAssembly
public import OverfullWork.KuhnOsthusPreprocessingConstruction
public import OverfullWork.OsthusStadenH1Profile

@[expose] public section


/-! Combine the physical chord and parity reserves in the complement
of preprocessing, as in Kühn–Osthus Lemma 11.2 and Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 950000 in
/-- Fixed chord and parity reserves give the regular reserve and
universal absorption property used in the final assembly. The
prepared rounds are required only for a regular ordinary residue
in the physical complement of these fixed arcs. -/
theorem kuhn_osthus_joint_absorption_reserve (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ} (_hn : 0 < n)
      (G PG B U E : Digraph W) (Z : Finset W) (c : ↥Zᶜ → Fin n)
      (r f q r₁ r₂ r₃ m K a : ℕ) (ε : ℝ),
      let t := r*(f*n)
      let s := r₁+r₂+r-(q-1)*r₃
      let X (j : Fin n) := (univ : Finset ↥Zᶜ).filter (fun v => c v = j)
      let CA := (U ⊔ E) ⊔ B
      let e := (exceptionalCoordinates Z).toEmbedding
      ∀ (P : Fin s → Digraph (↥Zᶜ ⊕ ↥Z)) (L : Fin s → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z)),
      let PC := liftDirectedPair e e (⨆ j, P j)
      let RB := CA ⊔ PC
      PG ≤ G → CA ≤ G \ PG →
      (∀ j, P j ≤ pullDirectedPair e e ((G \ PG) \ CA)) →
      (∀ j, AbsorbsWindingFactor X (P j) (L j)) →
      Pairwise (fun j l => Disjoint (P j) (P l)) →
      (∀ x, let d := match x with | .inl _ => 6*s | .inr _ => 7*s
        inDegree (⨆ j, P j) x = d ∧ outDegree (⨆ j, P j) x = d) →
      (∀ x, let d := if x ∈ Z then a else a+r
        inDegree PG x = d ∧ outDegree PG x = d) →
      (∀ x, let d := if x ∈ Z then q*r₃ else r₁+r₂+r₃
        inDegree CA x = d ∧ outDegree CA x = d) →
      Disjoint (U ⊔ E) B →
      N ≤ m → 0 ≤ ε → ε ≤ ρ/512 → (K:ℝ) ≤ (ρ/512)*(m:ℝ) →
      r*n*f^2 ≤ m → (16:ℝ) ≤ (ρ/128)^2*(f:ℝ) →
      0 < q → t = q*r₃ → t ≤ r₁+r₂+r+r₃ →
      (∀ j, (X j).card = m) →
      (∀ j, IsSuperregularPair (induced B Zᶜ) ε ρ (X j) (X (finRotate n j))) →
      (∀ x y, B.Adj x y → ∃ a b : ↥Zᶜ, a.val = x ∧ b.val = y ∧ c b = finRotate n (c a)) →
      (∀ H : Digraph W, H ≤ G \ RB →
        (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) →
        (∀ v : ↥Zᶜ, inDegree (induced H Zᶜ) v = r ∧ outDegree (induced H Zᶜ) v = r) →
        Nonempty (PreparedChordSystems (H ⊔ U ⊔ E) Z c (finRotate n) K
          (Fin r × Fin (f*n)))) →
      PG ⊔ RB ≤ G ∧ Disjoint PG RB ∧
      (∀ x, inDegree (PG ⊔ RB) x = a+r+r₁+r₂+r₃+6*s ∧
        outDegree (PG ⊔ RB) x = a+r+r₁+r₂+r₃+6*s) ∧
      ∀ H : Digraph W, H ≤ G \ RB →
        (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) →
        (∀ v : ↥Zᶜ, inDegree (induced H Zᶜ) v = r ∧ outDegree (induced H Zᶜ) v = r) →
        ∃ F : Fin (t+s*7) → Equiv.Perm W, matchingUnion F = H ⊔ RB ∧
          (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
          ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x := by
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_11_2_from_prepared_chord_rounds.{u} ρ hρ hρ₁
  refine ⟨N,?_⟩
  intro W _ n hn
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro G PG B U E Z c r f q r₁ r₂ r₃ m K a ε t s X CA e P L PC RB
    hPG hCA hP hAbsorb hDisP hDegP hDegPG hDegCA hDisB hNmin hε hTol hK hSize hScale
    hq ht hRoom hCard hPair hSupp hPrepared
  have hPC : PC ≤ (G \ PG) \ CA := by
    rintro x y ⟨u,v,rfl,rfl,huv⟩
    obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp huv
    exact hP j hj
  have hRB : RB ≤ G \ PG := sup_le hCA (fun _ _ h => (hPC h).1)
  have hPGRB : Disjoint PG RB := disjoint_iff_inf_le.mpr (fun _ _ h => (hRB h.2).2 h.1)
  have hCAPC : Disjoint CA PC := disjoint_iff_inf_le.mpr (fun _ _ h => (hPC h.2).2 h.1)
  have hDegPC (x : W) : let d := if x ∈ Z then 7*s else 6*s
      inDegree PC x = d ∧ outDegree PC x = d := by
    obtain ⟨v,rfl⟩ := (exceptionalCoordinates Z).surjective x
    have hi := lift_pair_semidegree e e (⨆ j, P j) false v
    have ho := lift_pair_semidegree e e (⨆ j, P j) true v
    change inDegree PC (e v) = inDegree (⨆ j, P j) v at hi
    change outDegree PC (e v) = outDegree (⨆ j, P j) v at ho
    change (inDegree PC (e v) = _) ∧ (outDegree PC (e v) = _)
    rw [hi,ho]
    cases v with
    | inl v =>
      have hv := mem_compl.mp v.prop
      change inDegree (⨆ j, P j) (.inl v) = (if v.val ∈ Z then 7*s else 6*s) ∧
        outDegree (⨆ j, P j) (.inl v) = (if v.val ∈ Z then 7*s else 6*s)
      rw [if_neg hv]
      exact hDegP (.inl v)
    | inr v =>
      change inDegree (⨆ j, P j) (.inr v) = (if v.val ∈ Z then 7*s else 6*s) ∧
        outDegree (⨆ j, P j) (.inr v) = (if v.val ∈ Z then 7*s else 6*s)
      rw [if_pos v.prop]
      exact hDegP (.inr v)
  have hDegRB (x : W) : let d := if x ∈ Z then q*r₃+7*s else r₁+r₂+r₃+6*s
      inDegree RB x = d ∧ outDegree RB x = d := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint CA PC (disjoint_iff_inf_le.mp hCAPC) x
    change inDegree (CA ⊔ PC) x = _ ∧ outDegree (CA ⊔ PC) x = _
    rw [hi,ho,(hDegCA x).1,(hDegCA x).2,(hDegPC x).1,(hDegPC x).2]
    by_cases hx : x ∈ Z <;> simp [hx]
  have hBalance : (q-1)*r₃+s = r₁+r₂+r := by
    have he : q*r₃ = (q-1)*r₃+r₃ := by
      rw [←Nat.add_one_mul,Nat.sub_add_cancel (by omega : 1 ≤ q)]
    dsimp only [s]
    omega
  refine ⟨sup_le hPG (fun _ _ h => (hRB h).1),hPGRB,
    kuhn_osthus_balanced_absorption_reserve PG RB Z a r r₁ r₂ r₃ q s hq hBalance hPGRB hDegPG hDegRB,?_⟩
  intro H hHLe hSuppH hRegH
  have hHRB : Disjoint H RB := disjoint_iff_inf_le.mpr (fun _ _ h => (hHLe h.1).2 h.2)
  have hHCA : Disjoint H CA := hHRB.mono_right le_sup_left
  have hHPC : Disjoint H PC := hHRB.mono_right le_sup_right
  have hDis : Disjoint (H ⊔ U ⊔ E) B := by
    rw [show H ⊔ U ⊔ E = H ⊔ (U ⊔ E) by ac_rfl,disjoint_sup_left]
    exact ⟨hHCA.mono_right le_sup_right,hDisB⟩
  let A := (H ⊔ U ⊔ E) ⊔ B
  have hA : A = H ⊔ CA := by dsimp only [A,CA]; ac_rfl
  have hDegH (x : W) : let d := if x ∈ Z then 0 else r
      inDegree H x = d ∧ outDegree H x = d := by
    let g : ↥Zᶜ ↪ W := Function.Embedding.subtype _
    have hIdent : H = liftDirectedPair g g (induced H Zᶜ) := by
      ext v w
      constructor
      · intro hvw
        have hh := hSuppH v w hvw
        exact ⟨⟨v,mem_compl.mpr hh.1⟩,⟨w,mem_compl.mpr hh.2⟩,rfl,rfl,hvw⟩
      · rintro ⟨v,w,rfl,rfl,h⟩
        exact h
    have hLift := ordinary_lift_degrees Z (induced H Zᶜ) x
    change (∀ hv : x ∉ Z, inDegree (liftDirectedPair g g (induced H Zᶜ)) x =
      inDegree (induced H Zᶜ) ⟨x,mem_compl.mpr hv⟩ ∧ outDegree (liftDirectedPair g g (induced H Zᶜ)) x =
      outDegree (induced H Zᶜ) ⟨x,mem_compl.mpr hv⟩) ∧
      (x ∈ Z → inDegree (liftDirectedPair g g (induced H Zᶜ)) x = 0 ∧
        outDegree (liftDirectedPair g g (induced H Zᶜ)) x = 0) at hLift
    rw [←hIdent] at hLift
    by_cases hx : x ∈ Z
    · simpa only [if_pos hx] using hLift.2 hx
    · have hi := (hLift.1 hx).1.trans (hRegH ⟨x,mem_compl.mpr hx⟩).1
      have ho := (hLift.1 hx).2.trans (hRegH ⟨x,mem_compl.mpr hx⟩).2
      simpa only [if_neg hx] using And.intro hi ho
  have hDegA (x : W) : let d := if x ∈ Z then t else r₁+r₂+r+r₃
      inDegree A x = d ∧ outDegree A x = d := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint H CA (disjoint_iff_inf_le.mp hHCA) x
    rw [hA,hi,ho,(hDegH x).1,(hDegH x).2,(hDegCA x).1,(hDegCA x).2]
    by_cases hx : x ∈ Z <;> simp [hx,ht,Nat.add_comm,Nat.add_left_comm]
  have hApart : Disjoint (pullDirectedPair e e A) (⨆ j, P j) := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨h,h'⟩
    have hArc : PC.Adj (e x) (e y) := (liftDirectedPair_adj e e _ x y).mpr h'
    change A.Adj (e x) (e y) at h
    rw [hA] at h
    rcases h with h | h
    · exact disjoint_iff_inf_le.mp hHPC ⟨h,hArc⟩
    · exact disjoint_iff_inf_le.mp hCAPC ⟨h,hArc⟩
  obtain ⟨Q⟩ := hPrepared H hHLe hSuppH hRegH
  obtain ⟨F,hF,hEdge,hCycle,_,_⟩ := hN B H U E Z c r f q r₁ r₂ r₃ m K ε Q
    hNmin hε hTol hK hSize hScale hq ht hCard hPair hDis hSupp hDegA P L hAbsorb hDisP hApart
  change matchingUnion F = A ⊔ PC at hF
  exact ⟨F,hF.trans (by rw [hA]; exact sup_assoc _ _ _),hCycle,hEdge⟩

/-- The budget calculations (11.9)–(11.14) with integral degrees.
The regular residue and the two absorber sizes are computed before
an approximate packing is selected. -/
theorem kuhn_osthus_absorption_degree_bounds
    (p a r₁ k f q r₃ ell g : ℕ) (ha : a ≤ p) (hk : 0 < k) (hq : 0 < q)
    (hf : f ≤ k) (hWalk : 96*ell*g^2 ≤ k) (hBudget : p*k^2 ≤ r₁) :
    let r := p-a
    let t := r*(f*k)
    let r₂ := 96*ell*g^2*k*r
    let s := r₁+r₂+r-(q-1)*r₃
    t = q*r₃ →
    a+r = p ∧ t ≤ r₁ ∧ r₂ ≤ r₁ ∧ r₃ ≤ r₁ ∧ (q-1)*r₃+s = r₁+r₂+r ∧
      p+r₁+r₂+r₃+6*s ≤ 22*r₁ := by
  intro r t r₂ s ht
  have hR : r ≤ p := Nat.sub_le _ _
  have hPk : p ≤ r₁ :=
    (Nat.le_mul_of_pos_right p (pow_pos hk _)).trans hBudget
  have hT : t ≤ r₁ := by
    calc
      t ≤ r*(k*k) := Nat.mul_le_mul_left r (Nat.mul_le_mul_right k hf)
      _ ≤ p*k^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hR
      _ ≤ r₁ := hBudget
  have hR₂ : r₂ ≤ r₁ := by
    calc
      r₂ = r*((96*ell*g^2)*k) := by dsimp only [r₂]; ring
      _ ≤ r*(k*k) := Nat.mul_le_mul_left r (Nat.mul_le_mul_right k hWalk)
      _ ≤ p*k^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hR
      _ ≤ r₁ := hBudget
  have hR₃ : r₃ ≤ r₁ := by
    have h := Nat.mul_le_mul_right r₃ (show 1 ≤ q by omega)
    rw [←ht,one_mul] at h
    exact h.trans hT
  have hBalance : (q-1)*r₃+s = r₁+r₂+r := by
    have h := Nat.mul_le_mul_right r₃ (Nat.sub_le q 1)
    rw [←ht] at h
    dsimp only [s]
    omega
  have hS : s ≤ r₁+r₂+r := Nat.sub_le _ _
  exact ⟨by dsimp only [r]; omega,hT,hR₂,hR₃,hBalance,by omega⟩

end OverfullWork.DirectedRobustExpansion
