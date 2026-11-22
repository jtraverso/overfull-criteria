module

public import OverfullWork.KuhnOsthusCommonWoundFactors

@[expose] public section


/-! Compare all three applications of Lemma 7.6 on one partition. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

open Finset in
/-- Translate the exceptional-set bound in (11.6) from total volume
to ordinary volume. The parameter `base` counts the vertices of a
whole wound cluster, before subdividing it into styles. -/
theorem wound_exceptional_density_of_partition {V : Type*} [Fintype V] {n : ℕ}
    (X : Fin n → Finset V) (Z : Finset V) (base : ℕ) (ζ : ℝ)
    (hSize : ∀ i, (X i).card = base)
    (hApart : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hOrdinary : ∀ i, Disjoint (X i) Z)
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ X i)
    (hζHalf : ζ ≤ 1/2)
    (hZ : (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ)) :
    Z.card+n*base = Fintype.card V ∧ (Z.card:ℝ) ≤ (2*ζ)*((n*base:ℕ):ℝ) := by
  classical
  let U := (univ : Finset (Fin n)).biUnion X
  have hU : U = Zᶜ := by
    ext x
    rw [mem_compl]
    exact ⟨fun hx hz => by
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
      exact disjoint_left.mp (hOrdinary i) hi hz,
      fun hx => by
        obtain ⟨i,hi⟩ := hCover x hx
        exact mem_biUnion.mpr ⟨i,mem_univ _,hi⟩⟩
  have hCard : U.card = n*base := by
    rw [card_biUnion (fun i _ j _ hij => hApart i j hij)]
    simp [hSize]
  have hMass : Z.card+n*base = Fintype.card V := by
    rw [←hCard,hU,card_compl]
    exact Nat.add_sub_of_le (card_le_univ Z)
  refine ⟨hMass,?_⟩
  rw [←hMass, Nat.cast_add] at hZ
  have hHalf := mul_le_mul_of_nonneg_right hζHalf (show (0:ℝ) ≤ Z.card by positivity)
  nlinarith only [hHalf,hZ]

/-- The total ordinary volume is the same in all three windings.
An upper bound for the number of style-interval slots gives common
margins for the endpoint count and the reduced routing budget. -/
theorem wound_factor_counts_from_common_density
    (L k base m K l b c z Λ r priorLoss : ℕ) (α θ σ μ ζ χ : ℝ)
    (hWinding : L = l*b) (hCell : base = K*m) (hSlots : K*l ≤ Λ)
    (hb : 6 ≤ b) (hk : 0 < k) (hm : 0 < m) (hc : 0 < c)
    (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hσ : σ ≤ 1/2) (hμ : 0 < μ) (hζ : 0 ≤ ζ) (hχ : 0 ≤ χ)
    (hExceptional : (z:ℝ) ≤ ζ*((L*k*base:ℕ):ℝ))
    (hDegrees : ((K*l*r+priorLoss:ℕ):ℝ) ≤ χ*((L*k*base:ℕ):ℝ))
    (hEndpoint : (Λ:ℝ)*((4*(c:ℝ)+2)*ζ+χ) < θ*(α/3)^2/4)
    (hRouting : (Λ:ℝ)*ζ*(8/(μ^2/2)+6) < (μ^2/2)/(32*(c:ℝ))) :
    (((4*c+2)*z+K*l*r+priorLoss:ℕ):ℝ) <
      (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*((1-σ)*(θ*(α/3)*(m:ℝ))) ∧
    (z:ℝ)*(8/(μ^2/2)+6) < ((m:ℝ)/(2*(c:ℝ)))*((μ^2/2)*((b*k:ℕ):ℝ)/16) := by
  let W : ℝ := (b:ℝ)*(k:ℝ)*(m:ℝ)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hVolume : ((L*k*base:ℕ):ℝ) = (K:ℝ)*(l:ℝ)*W := by
    rw [hWinding,hCell]
    dsimp only [W]
    push_cast
    ring
  have hSlotReal : (K:ℝ)*(l:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hSlots
  have hMass : ((L*k*base:ℕ):ℝ) ≤ (Λ:ℝ)*W := by
    rw [hVolume]
    exact mul_le_mul_of_nonneg_right hSlotReal hW.le
  have hZ : (z:ℝ) ≤ ζ*((Λ:ℝ)*W) := hExceptional.trans (mul_le_mul_of_nonneg_left hMass hζ)
  have hD : ((K*l*r+priorLoss:ℕ):ℝ) ≤ χ*((Λ:ℝ)*W) :=
    hDegrees.trans (mul_le_mul_of_nonneg_left hMass hχ)
  have hB : (b:ℝ)/2 ≤ ((b-3:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 3 ≤ b)]
    have h : (6:ℝ) ≤ b := by exact_mod_cast hb
    norm_num
    linarith only [h]
  constructor
  · have hTotal : (((4*c+2)*z+K*l*r+priorLoss:ℕ):ℝ) ≤ ((Λ:ℝ)*((4*(c:ℝ)+2)*ζ+χ))*W := by
      have h := mul_le_mul_of_nonneg_left hZ (show (0:ℝ) ≤ 4*(c:ℝ)+2 by positivity)
      push_cast at hD ⊢
      linarith only [h,hD]
    refine hTotal.trans_lt ((mul_lt_mul_of_pos_right hEndpoint hW).trans_le ?_)
    calc
      (θ*(α/3)^2/4)*W = (α/3*(k:ℝ))*((b:ℝ)/2)*((1/2:ℝ)*(θ*(α/3)*(m:ℝ))) := by dsimp only [W]; ring
      _ ≤ _ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hB (by positivity)
        · exact mul_le_mul_of_nonneg_right (by linarith only [hσ]) (by positivity)
        · positivity
        · positivity
  · have hFactor : 0 ≤ 8/(μ^2/2)+6 := by positivity
    have hZ' := mul_le_mul_of_nonneg_right hZ hFactor
    refine hZ'.trans_lt ?_
    calc
      ζ*((Λ:ℝ)*W)*(8/(μ^2/2)+6) = ((Λ:ℝ)*ζ*(8/(μ^2/2)+6))*W := by ring
      _ < ((μ^2/2)/(32*(c:ℝ)))*W := mul_lt_mul_of_pos_right hRouting hW
      _ = _ := by
        dsimp only [W]
        have hcp : (c:ℝ) ≠ 0 := by exact_mod_cast hc.ne'
        push_cast
        field_simp
        ring

open Finset in
/-- Exact degrees of the earlier reserves give the three losses for
Lemma 7.6. The exceptional bound is kept separate for endpoint
counts, even for the union of preprocessing and the chord absorber. -/
theorem wound_exceptional_stage_degrees {V : Type*} [Fintype V]
    (G PG CA : Digraph V) (Z : Finset V) (a t q r₁ r₂ r₃ : ℕ)
    (hPG : PG ≤ G) (hCA : CA ≤ G \ PG) (hExc : q*r₃ ≤ r₁+r₂+r₃)
    (hDegreePG : ∀ x, let d := if x ∈ Z then a else a+t
      inDegree PG x = d ∧ outDegree PG x = d)
    (hDegreeCA : ∀ x, let d := if x ∈ Z then q*r₃ else r₁+r₂+r₃
      inDegree CA x = d ∧ outDegree CA x = d) :
    PG ⊔ CA ≤ G ∧
    (∀ x, inDegree PG x ≤ a+t ∧ outDegree PG x ≤ a+t) ∧
    (∀ x ∈ Z, inDegree PG x = a ∧ outDegree PG x = a) ∧
    (∀ x, inDegree (PG ⊔ CA) x ≤ a+t+r₁+r₂+r₃ ∧ outDegree (PG ⊔ CA) x ≤ a+t+r₁+r₂+r₃) ∧
    (∀ x ∈ Z, inDegree (PG ⊔ CA) x = a+q*r₃ ∧ outDegree (PG ⊔ CA) x = a+q*r₃) ∧
    ∀ x ∉ Z, inDegree (PG ⊔ CA) x = a+t+r₁+r₂+r₃ ∧ outDegree (PG ⊔ CA) x = a+t+r₁+r₂+r₃ := by
  have hApart (x y : V) (h : PG.Adj x y ∧ CA.Adj x y) : False := (hCA h.2).2 h.1
  have hDegreeUnion (x : V) : let d := if x ∈ Z then a+q*r₃ else a+t+r₁+r₂+r₃
      inDegree (PG ⊔ CA) x = d ∧ outDegree (PG ⊔ CA) x = d := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint PG CA hApart x
    rw [hi,ho,(hDegreePG x).1,(hDegreePG x).2,(hDegreeCA x).1,(hDegreeCA x).2]
    split_ifs <;> omega
  refine ⟨sup_le hPG (fun _ _ h => (hCA h).1),?_,?_,?_,?_,?_⟩
  · intro x
    obtain ⟨hi, ho⟩ := hDegreePG x
    by_cases ha : x ∈ Z
    · rw [if_pos ha] at hi ho
      omega
    · rw [if_neg ha] at hi ho
      omega
  · intro x hx
    simpa only [if_pos hx] using hDegreePG x
  · intro x
    obtain ⟨hi, ho⟩ := hDegreeUnion x
    by_cases ha : x ∈ Z
    · rw [if_pos ha] at hi ho
      omega
    · rw [if_neg ha] at hi ho
      omega
  · intro x hx
    simpa only [if_pos hx] using hDegreeUnion x
  · intro x hx
    simpa only [if_neg hx] using hDegreeUnion x

/-- Bounds for the factor multiplicity plus earlier exceptional loss
in the three applications of Lemma 7.6, using (11.9)–(11.13).
The two ordinary deletion bounds used for pair regularity are
smaller and are recorded separately. -/
theorem wound_exceptional_counts_of_absorption_degrees
    (l r₀ p a r₁ r₂ r₃ q s : ℕ)
    (ha : a = 50*l*r₀) (hpa : a ≤ p) (hp : p ≤ r₁)
    (h₂ : r₂ ≤ r₁) (h₃ : r₃ ≤ r₁) (hq : q*r₃ ≤ r₁)
    (hs : (q-1)*r₃+s = r₁+r₂+(p-a)) :
    50*l*r₀ ≤ p ∧ q*r₃+a ≤ 2*r₁ ∧ 7*s+(a+q*r₃) ≤ 23*r₁ ∧
      p+r₁+r₂+r₃ ≤ 4*r₁ ∧ s ≤ 3*r₁ := by
  omega

end OverfullWork.DirectedRobustExpansion
