module

public import OverfullWork.KuhnOsthusPreprocessingScales
public import OverfullWork.KuhnOsthusSetupDivisibility

@[expose] public section


/-! Specialize the numerical inputs of Lemma 7.6 to the three
windings in the proof of Kühn–Osthus Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Choose the same winding for the interval lengths of all three
applications. Each interval contains at least six coarse circuits,
which is enough for the bound on eligible endpoint cells. -/
theorem exists_kuhn_osthus_exceptional_windings (l g fMin qMin : ℕ)
    (hl : 2 ≤ l) (hg : 0 < g) :
    ∃ f q b₈ b₁₀ : ℕ, max (6*l) (max 42 fMin) ≤ f ∧ max 15 qMin ≤ q ∧
      g ∣ f ∧ f ∣ q ∧ 0 < q/f ∧ (q/f)*f = q ∧ f ≤ q/f ∧ 6 ≤ b₈ ∧ 6 ≤ b₁₀ ∧
      f^2 = l*b₈ ∧ f^2 = f*f ∧ f^2 = 7*b₁₀ := by
  obtain ⟨f,q,b₈,b₁₀,hf,hq,hfMin,hqMin,hGF,hFQ,hRatio,_,_,hW⟩ :=
    exists_kuhn_osthus_common_winding_depths l g (max (6*l) (max 42 fMin)) (max 15 qMin) hl hg
  obtain ⟨h₈,h₉,h₁₀⟩ := hW 1
  simp only [Nat.mul_one] at h₈ h₉ h₁₀
  have hQ := Nat.div_mul_cancel hFQ
  have hfSq : f ≤ f^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ hf
  have hlSq : l*6 ≤ l*b₈ := by
    rw [←h₈,mul_comm l]
    exact ((le_max_left _ _).trans hfMin).trans hfSq
  have hb₈ : 6 ≤ b₈ := Nat.le_of_mul_le_mul_left hlSq (by omega)
  have hf42 : 42 ≤ f := (le_max_left _ _).trans ((le_max_right _ _).trans hfMin)
  have hb₁₀ : 6 ≤ b₁₀ := by rw [h₁₀] at hfSq; omega
  have hP : 0 < q/f := Nat.pos_of_ne_zero (fun h => by rw [h,zero_mul] at hQ; omega)
  exact ⟨f,q,b₈,b₁₀,hfMin,hqMin,hGF,hFQ,hP,hQ,hRatio,hb₈,hb₁₀,h₈,h₉,h₁₀⟩

/-- The size modulus in (11.6) gives physical cells for 50, q/f,
and one style. A single bound on the original cluster size covers
any common lower bound on the three subdivided cell sizes. -/
theorem kuhn_osthus_exceptional_style_cell_sizes (f q ℓ base T : ℕ)
    (hq : 0 < q) (hFQ : f ∣ q) (hℓ : 0 < ℓ)
    (hDiv : 200*ℓ*(q/f) ∣ base) (hSize : max 50 (q/f)*T ≤ base) :
    ∃ m₈ m₉ half : ℕ, base = 50*m₈ ∧ base = (q/f)*m₉ ∧
      f*base = q*m₉ ∧ base = 2*half ∧ T ≤ m₈ ∧ T ≤ m₉ ∧ T ≤ base := by
  obtain ⟨hPos,h₈,h4,m₉,hm₉,hF⟩ :=
    kuhn_osthus_cluster_size_divisibilities f q ℓ base hq hFQ hℓ hDiv
  obtain ⟨m₈,hm₈⟩ := h₈
  have hEven : 2 ∣ 4*ℓ := ⟨2*ℓ,by omega⟩
  obtain ⟨half,hHalf⟩ := hEven.trans h4
  have hP : 0 < q/f := Nat.pos_of_ne_zero (fun h => by rw [h,mul_zero] at hPos; omega)
  have hT (K : ℕ) (hK : K ≤ max 50 (q/f)) : K*T ≤ base :=
    (Nat.mul_le_mul_right _ hK).trans hSize
  have hT₈ := hT 50 (le_max_left _ _)
  have hT₉ := hT (q/f) (le_max_right _ _)
  rw [hm₈] at hT₈
  rw [hm₉] at hT₉
  refine ⟨m₈,m₉,half,hm₈,hm₉,hF,hHalf,Nat.le_of_mul_le_mul_left hT₈ (by decide),
    Nat.le_of_mul_le_mul_left hT₉ hP,?_⟩
  exact (by omega : T ≤ 50*T).trans (hT 50 (le_max_left _ _))

/-- The seven equal intervals use the coordinates of Lemma 10.5.
Its integer parameter comes from the total cluster count. -/
theorem kuhn_osthus_parity_cluster_coordinates (n intervalSize : ℕ)
    (hSeven : n = 7*intervalSize) (hEven : 14 ∣ n) (hLarge : 210 ≤ n) :
    ∃ q : ℕ, 15 ≤ q ∧ intervalSize = 2*q ∧ n = 14*q := by
  obtain ⟨q,hq⟩ := hEven
  exact ⟨q,by omega,by omega,hq⟩

/-- A local tolerance and two positive rates for a fixed style count.
The factor rate is relative to a subdivided cell and the old-reserve
rate to the original wound cluster. Taking these margins separately
allows the final application with one style to use a larger error. -/
theorem exists_wound_factor_local_margins (K : ℕ) (α θ d ε : ℝ)
    (hα : 0 < α) (hθ : 0 < θ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hd : 6*ε ≤ d) :
    ∃ σ δ η a ρ lossRate : ℝ,
      0 < σ ∧ σ ≤ 1/2 ∧ σ ≤ θ*(α/3) ∧ 0 < δ ∧ δ ≤ 1 ∧ 4*δ ≤ ε ∧
      0 < η ∧ η ≤ 1/4 ∧ 0 < a ∧ K*σ ≤ η ∧ 2*(σ+a) ≤ η ∧ η < d-σ-a ∧
      2*σ ≤ d ∧ 2*(max 2 (K:ℝ)*σ+a) ≤ δ ∧
      0 < ρ ∧ ρ ≤ a*η ∧ ρ ≤ a*δ ∧ 0 < lossRate ∧ lossRate = (σ/4)*σ := by
  let δ := ε/4
  let η := δ/4
  let a := η/4
  let k := max 2 (K:ℝ)
  let σ := min (θ*(α/3)) (η/(4*k))
  have hk : 0 < k := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_max_left _ _)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hσ : 0 < σ := lt_min (by positivity) (div_pos hη (by positivity))
  have hσTheta : σ ≤ θ*(α/3) := min_le_left _ _
  have hkσ : k*σ ≤ η/4 := by
    have h := (le_div_iff₀ (show 0 < 4*k by positivity)).mp
      (show σ ≤ η/(4*k) from min_le_right _ _)
    linarith only [h]
  have hKσ : (K:ℝ)*σ ≤ k*σ := mul_le_mul_of_nonneg_right (le_max_right _ _) hσ.le
  have hσ₄ : σ ≤ η/4 := by
    have h := mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ k from le_max_left _ _) hσ.le
    linarith only [h,hkσ,hσ]
  have hδEq : 4*δ = ε := by dsimp [δ]; ring
  have hηEq : 4*η = δ := by dsimp [η]; ring
  have haEq : 4*a = η := by dsimp [a]; ring
  have hρη : a*η ≤ a*δ := mul_le_mul_of_nonneg_left (by linarith only [hη,hηEq]) ha.le
  refine ⟨σ,δ,η,a,a*η,(σ/4)*σ,hσ,?_,hσTheta,hδ,?_,hδEq.le,hη,?_,ha,?_,?_,?_,?_,?_,
    mul_pos ha hη,le_rfl,hρη,by positivity,rfl⟩
  all_goals linarith only [hε₁,hd,hδEq,hηEq,haEq,hσ₄,hη,hε,hkσ,hKσ]

/-- The three multiplicity rates are measured against the actual style
cell for that application. For chords the change of cell size cancels
the factor f/q in the count of exceptional factors, as in (11.12). -/
theorem wound_exceptional_factor_rates
    (f q n base m₈ m₉ r₀ p a r₁ r₃ s : ℕ) (ρ₈ ρ₉ ρ₁₀ : ℝ)
    (hf : 0 < f) (hq : 0 < q)
    (hBase₈ : base = 50*m₈) (hBase₉ : f*base = q*m₉)
    (hChord : q*r₃ = (p-a)*(f*n)) (hs : s ≤ 3*r₁)
    (hPre : 50*(r₀:ℝ) ≤ ρ₈*(base:ℝ))
    (hRes : (p:ℝ)*(n:ℝ) ≤ ρ₉*(base:ℝ))
    (hParity : 3*(r₁:ℝ) ≤ ρ₁₀*(base:ℝ)) :
    (r₀:ℝ) ≤ ρ₈*(m₈:ℝ) ∧ (r₃:ℝ) ≤ ρ₉*(m₉:ℝ) ∧ (s:ℝ) ≤ ρ₁₀*(base:ℝ) := by
  have hBase₈' : (base:ℝ) = 50*(m₈:ℝ) := by exact_mod_cast hBase₈
  have hBase₉' : (f:ℝ)*(base:ℝ) = (q:ℝ)*(m₉:ℝ) := by exact_mod_cast hBase₉
  have hChord' : (q:ℝ)*(r₃:ℝ) = ((p-a:ℕ):ℝ)*((f:ℝ)*(n:ℝ)) := by exact_mod_cast hChord
  refine ⟨?_,?_,(by exact_mod_cast hs : (s:ℝ) ≤ 3*(r₁:ℝ)).trans hParity⟩
  · rw [hBase₈'] at hPre
    linarith only [hPre]
  · apply (mul_le_mul_iff_of_pos_left (show (0:ℝ) < q by exact_mod_cast hq)).mp
    have hRes' := mul_le_mul_of_nonneg_left hRes (show (0:ℝ) ≤ f by exact_mod_cast hf.le)
    have hSub : ((p-a:ℕ):ℝ) ≤ p := by exact_mod_cast Nat.sub_le p a
    have hUp := mul_le_mul_of_nonneg_right hSub (show 0 ≤ (f:ℝ)*(n:ℝ) by positivity)
    nlinarith only [hChord',hBase₉',hRes',hUp,
      congrArg (fun x : ℝ => ρ₉*x) hBase₉']

end OverfullWork.DirectedRobustExpansion
