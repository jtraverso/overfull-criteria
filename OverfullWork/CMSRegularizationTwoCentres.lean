module

public import OverfullWork.CMSRegularizationDeficitBase

@[expose] public section


/-! Exceptional odd cuts for the two identified vertices in CMS
Subcase 2.4. Each copy is charged the weak VAL degree bound at its
original endpoint before identification. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion OrderedCanonicalTransport
open scoped Classical

theorem internal_bundles_le_of_weighted_val (da db x y f z : ℕ)
    (hOrder : da ≤ db) (hA : (f+2)*x ≤ da) (hB : (f+2)*y ≤ db)
    (hRow : z ≤ db-da) (hDeficit : z ≤ f) : x+y+z ≤ db := by
  by_cases hZero : x+y = 0
  · omega
  have hWeight : f+2 ≤ db := by
    have hx : 1 ≤ x+y := by omega
    have hh := Nat.mul_le_mul_left (f+2) hx
    by_cases hX : x = 0
    · simpa only [hX,zero_add,mul_one] using hh.trans (by simpa [hX] using hB)
    · have hx' : 1 ≤ x := by omega
      have hh' := Nat.mul_le_mul_left (f+2) hx'
      simpa only [mul_one] using hh'.trans (hA.trans hOrder)
  have hSum : (f+2)*(x+y) ≤ 2*db := by rw [Nat.mul_add]; omega
  have hCap : 2*db ≤ (f+2)*(db-f) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hWeight
    have he : db-f = k+2 := by omega
    rw [he,hk]
    nlinarith only [Nat.zero_le (f*k)]
  have hBundle := Nat.le_of_mul_le_mul_left (hSum.trans hCap) (by omega : 0 < f+2)
  omega

variable {m d : ℕ} {D : MultiGraph (Fin (m+1) × Bool)}

set_option maxHeartbeats 1800000 in
theorem Completion.two_centre_triples_safe (C : Completion D d) (hD : ∀ v, D.degree v ≤ d)
    (hNo : ¬D.HasOverfullSubset d)
    (hOrder : D.degree (0,false) ≤ D.degree (0,true))
    (hAB : D.mult s((0,false),(0,true)) = 0)
    (hWeighted : ∀ v, v ≠ (0,false) → v ≠ (0,true) → ∀ j : Bool,
      (d-D.degree v+2)*D.mult s((0,j),v) ≤ D.degree (0,j)) :
    ∀ v, v ≠ (0,false) → v ≠ (0,true) →
      d ≤ ((D.addCopies C.L).addCopies C.N).cutSize {(0,false),(0,true),v} := by
  let W := Fin (m+1) × Bool
  let a : W := (0,false)
  let b : W := (0,true)
  let M := (D.addCopies C.L).addCopies C.N
  change D.degree a ≤ D.degree b at hOrder
  have hab : a ≠ b := by intro h; cases congrArg Prod.snd h
  have hLa : C.L.degree a = D.degree b-D.degree a := by
    have hh := (C.prefix_degrees 0 C.positive).1
    change C.L.degree a = (d-D.degree a)-(d-D.degree b) at hh
    have ha := hD a
    have hb := hD b
    omega
  have hLb : C.L.degree b = 0 := (C.prefix_degrees 0 C.positive).2
  have hLzero (v : W) : C.L.mult s(b,v) = 0 := by
    have hh := C.L.mult_pair_le_degree b v
    rw [hLb] at hh
    omega
  have hNa : C.N.degree a = d-D.degree b := by
    have hh := C.regular a
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies,hLa] at hh
    have hda := hD a
    have hdb := hD b
    omega
  have hNb : C.N.degree b = d-D.degree b := by
    have hh := C.regular b
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies,hLb] at hh
    omega
  intro v hva hvb
  change v ≠ a at hva
  change v ≠ b at hvb
  change d ≤ M.cutSize {a,b,v}
  have hSplit : d ≤ M.cutSize {a,b,v} ∨ (C.N.mult s(a,v) = 0 ∧ C.N.mult s(b,v) = 0) := by
    by_cases hTwo : 2 ≤ C.k
    · right
      have hPair := C.first_bundle_lower_of_prefix_two hTwo
      change d-D.degree b ≤ C.N.mult s(a,b) at hPair
      have ha := CanonicalTripleAddition.two_bundles_le_degree C.N a b v hvb.symm
      have hb := CanonicalTripleAddition.two_bundles_le_degree C.N b a v hva.symm
      rw [Sym2.eq_swap (a := b) (b := a),hNb] at hb
      rw [hNa] at ha
      omega
    have hk : C.k = 1 := by have hp := C.positive; omega
    have hkm : C.k < m+1 := by
      by_contra! hn
      have hm : m = 0 := by omega
      subst m
      obtain ⟨i,j⟩ := v
      have hi : i = 0 := Fin.ext (by have hh := i.isLt; change i.val = 0; omega)
      subst i
      cases j
      · exact hva rfl
      · exact hvb rfl
    have ha : C.lastFalse = a := by
      apply Prod.ext
      · apply Fin.ext; change C.k-1 = 0; omega
      · rfl
    have hb : C.lastTrue = b := by
      apply Prod.ext
      · apply Fin.ext; change C.k-1 = 0; omega
      · rfl
    by_cases hm : v = C.middleVertex hkm
    · left
      simpa only [Completion.triangle,ha,hb,←hm] using C.triangle_safe_of_prefix_one hkm hk hD hNo
    · right
      have hv : v ∉ C.triangle hkm := by simp [Completion.triangle,ha,hb,hva,hvb,hm]
      have hNz := C.N_degree_zero_outside_triangle_of_prefix_one hkm hk v hv
      have hAv := C.N.mult_pair_le_degree v a
      have hBv := C.N.mult_pair_le_degree v b
      rw [Sym2.eq_swap (a := v),hNz] at hAv hBv
      omega
  rcases hSplit with hSafe | ⟨hAz,hBz⟩
  · exact hSafe
  have hLab := hLzero a
  rw [Sym2.eq_swap (a := b)] at hLab
  have hMab : M.mult s(a,b) ≤ d-D.degree b := by
    have hh := C.N.mult_pair_le_degree a b
    change D.mult s(a,b)+C.L.mult s(a,b)+C.N.mult s(a,b) ≤ _
    rw [hAB,hLab]
    omega
  have hAv := C.L.mult_pair_le_degree a v
  have hV := C.L.mult_pair_le_degree v a
  rw [hLa] at hAv
  rw [Sym2.eq_swap (a := v)] at hV
  have hV' := hV.trans (C.additions_bounded v)
  have hBound := internal_bundles_le_of_weighted_val (D.degree a) (D.degree b)
    (D.mult s(a,v)) (D.mult s(b,v)) (d-D.degree v) (C.L.mult s(a,v))
    hOrder (hWeighted v hva hvb false) (hWeighted v hva hvb true) hAv hV'
  have hMv : M.mult s(a,v)+M.mult s(b,v) ≤ D.degree b := by
    change D.mult s(a,v)+C.L.mult s(a,v)+C.N.mult s(a,v)+
      (D.mult s(b,v)+C.L.mult s(b,v)+C.N.mult s(b,v)) ≤ _
    rw [hAz,hBz,hLzero]
    omega
  have h := CriticalCentreTriples.triple_cut_identity M a b v hab hva.symm hvb.symm
  rw [C.regular a,C.regular b,C.regular v] at h
  have hb := hD b
  omega

set_option maxHeartbeats 1800000 in
theorem cms_regularization_dense_two_centres (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {m : ℕ} (D : MultiGraph (Fin (m+1) × Bool)) (d : ℕ),
          let W := Fin (m+1) × Bool
          let a : W := (0,false)
          let b : W := (0,true)
          let n := Fintype.card W
          N ≤ n → d < n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v, D.degree v ≤ d) → ¬D.HasOverfullSubset d →
          (∀ i : Fin (m+1), D.degree (i,false) ≤ D.degree (i,true)) →
          (∀ i j : Fin (m+1), i.val < j.val → D.degree (i,true) ≤ D.degree (j,false)) →
          D.mult s(a,b) = 0 →
          (∀ v, v ≠ a → v ≠ b → ∀ j : Bool, (d-D.degree v+2)*D.mult s((0,j),v) ≤ D.degree (0,j)) →
          (D.degree b : ℝ) ≤ 10*η*(n:ℝ) →
          (∀ v, v ≠ a → v ≠ b → (D.mult s(a,v):ℝ) ≤ 2*η^2*(n:ℝ)) →
          (∀ v, v ≠ a → v ≠ b → (d:ℝ)-6*η*(n:ℝ) ≤ (D.supportGraph.degree v:ℝ)) →
          IsRealRobust D.supportGraph ν τ →
          ∃ C : Completion D d, Nonempty (((D.addCopies C.L).addCopies C.N).EdgeColoring d) := by
  obtain ⟨τ,hτ,hGeneral⟩ := cms_regularization_of_local_profiles α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hGeneral ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηCap
  obtain ⟨N,hN⟩ := hUse η hη hηCap
  refine ⟨N,?_⟩
  intro m D d W a b n hSize hd hRel hD hNo hPair hOrder hAB hWeighted hSmall hBase hOrd hRob
  apply hN D d hSize hd hRel hD hNo hPair hOrder hBase _ _ hRob
  · intro x hxa hxb k
    have hRatio : (((k-1:ℕ):ℝ)/(k:ℝ)) ≤ 1 := by
      by_cases hp : k = 0
      · simp [hp]
      · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hp) : (0:ℝ) < k)).mpr
        exact_mod_cast Nat.sub_le k 1
    have hh := mul_le_mul_of_nonneg_right hRatio (Nat.cast_nonneg (α := ℝ) d)
    linarith only [hh,hOrd x hxa hxb]
  · intro C M
    have hB := C.second_anchor_profile_of_dense_base (6*η*(n:ℝ)) (10*η*(n:ℝ))
      (by positivity) hOrd (by linarith only [hSmall,Nat.cast_nonneg (α := ℝ) (D.supportGraph.degree b)])
    refine ⟨?_,?_,C.two_centre_triples_safe hD hNo (hPair 0) hAB hWeighted⟩
    · linarith only [hB]
    · intro x hxa hxb
      have hh := (hOrd x hxa hxb).trans (show (D.supportGraph.degree x:ℝ) ≤ M.supportGraph.degree x by
        exact_mod_cast C.support_degree_mono x)
      linarith only [hh,Nat.cast_nonneg (α := ℝ) (M.mult s(a,x))]

end OverfullWork.CanonicalRegularization
