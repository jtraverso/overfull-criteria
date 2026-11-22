module

public import OverfullWork.CMSRegularizationDenseBase

@[expose] public section


/-! The deficit-budget alternative of CMS Claim 4.3 with a simple
second vertex, including the exceptional odd cuts. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion OrderedCanonicalTransport
open scoped Classical

set_option maxHeartbeats 1800000 in
theorem cms_regularization_deficit_simple_second_away_from_first (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
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
          D.IsStarAt a → (∀ v, v ≠ a → D.mult s(b,v) ≤ 1) →
          (∀ v, v ≠ a → v ≠ b → (D.mult s(a,v):ℝ) ≤ 2*η^2*(n:ℝ)) →
          ((∑ v ∈ univ.erase a, (d-D.degree v))+D.degree a : ℕ) ≤ (d:ℝ)+5*η*(n:ℝ) →
          (((D.supportGraph.neighborFinset a).erase b).card ≤ 1 →
            (∃ w : W, w ≠ a ∧ w ≠ b ∧ D.degree w < d ∧
              ∀ v, v ∉ ({a,b,w}:Finset W) → D.degree v = d) ∨
            ∀ v, v ≠ a → v ≠ b → d ≤ D.cutSize {a,b,v}) →
          IsRealRobust D.supportGraph ν τ →
          ∃ C : Completion D d, Nonempty (((D.addCopies C.L).addCopies C.N).EdgeColoring d) := by
  obtain ⟨τ,hτ,hGeneral⟩ := cms_regularization_of_local_profiles α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨η₀,hη₀,hUse⟩ := hGeneral ν hν hντ
  let ηMax := min η₀ (1/2)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηCap
  obtain ⟨N,hN⟩ := hUse η hη (hηCap.trans (min_le_left _ _))
  refine ⟨N,?_⟩
  intro m D d W a b n hSize hd hRel hD hNo hPair hOrder hStar hSimple hBase hBud hLocal hRob
  let E := ⌊5*η*(n:ℝ)⌋₊
  let Y := ⌊2*η^2*(n:ℝ)⌋₊
  have hE : (E:ℝ) ≤ 5*η*(n:ℝ) := Nat.floor_le (by positivity)
  have hY : (Y:ℝ) ≤ 2*η^2*(n:ℝ) := Nat.floor_le (by positivity)
  have hQuad : 2*η^2*(n:ℝ) ≤ η*(n:ℝ) := by
    have hHalf : η ≤ 1/2 := hηCap.trans (min_le_right _ _)
    have hh := mul_nonneg hη (sub_nonneg.mpr hHalf)
    exact mul_le_mul_of_nonneg_right (show 2*η^2 ≤ η by nlinarith only [hh]) (Nat.cast_nonneg _)
  have hBudget : (∑ v ∈ univ.erase a, (d-D.degree v))+D.degree a ≤ d+E := by
    have hh := Nat.le_floor hBud
    rw [add_comm (d:ℝ),Nat.floor_add_natCast (by positivity : 0 ≤ 5*η*(n:ℝ))] at hh
    simpa only [E,Nat.add_comm] using hh
  have hBaseN (v : W) (hva : v ≠ a) (hvb : v ≠ b) : D.mult s(a,v) ≤ Y :=
    Nat.le_floor (hBase v hva hvb)
  obtain ⟨C⟩ := CanonicalNoOverfullCompletion.exists_completion_of_no_overfull D d hD hPair hOrder hNo
  have hProfile := C.local_profiles_of_star_deficits E Y hD hPair hOrder hStar hBudget
  apply hN D d hSize hd hRel hD hNo hPair hOrder hBase _ _ hRob
  · intro v hva hvb k
    have hh := hProfile.2 v hva (hBaseN v hva hvb)
    dsimp at hh
    push_cast at hh
    linarith only [hh,hE,hY,hQuad]
  · intro C' M
    have hLocalRows := (C'.local_profiles_of_star_deficits E Y hD hPair hOrder hStar hBudget).1
    have hb : b ≠ a := by intro he; cases congrArg Prod.snd he
    have hRow (v : W) (hva : v ≠ a) :
        (d:ℝ) ≤ (M.supportGraph.degree v:ℝ)+(M.mult s(a,v):ℝ)+(E:ℝ) := by
      exact_mod_cast hLocalRows v hva
    refine ⟨?_,?_,C'.simple_second_triples_safe_away_from_first hD hNo (hPair 0) hSimple hLocal⟩
    · linarith only [hRow b hb,hE,mul_nonneg hη (Nat.cast_nonneg (α := ℝ) n)]
    · intro v hva _
      linarith only [hRow v hva,hE,mul_nonneg hη (Nat.cast_nonneg (α := ℝ) n)]

theorem cms_regularization_deficit_simple_second (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
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
          D.IsStarAt a → (∀ v, D.mult s(b,v) ≤ 1) →
          (∀ v, v ≠ a → v ≠ b → (D.mult s(a,v):ℝ) ≤ 2*η^2*(n:ℝ)) →
          ((∑ v ∈ univ.erase a, (d-D.degree v))+D.degree a : ℕ) ≤ (d:ℝ)+5*η*(n:ℝ) →
          (((D.supportGraph.neighborFinset a).erase b).card ≤ 1 →
            (∃ w : W, w ≠ a ∧ w ≠ b ∧ D.degree w < d ∧
              ∀ v, v ∉ ({a,b,w}:Finset W) → D.degree v = d) ∨
            ∀ v, v ≠ a → v ≠ b → d ≤ D.cutSize {a,b,v}) →
          IsRealRobust D.supportGraph ν τ →
          ∃ C : Completion D d, Nonempty (((D.addCopies C.L).addCopies C.N).EdgeColoring d) := by
  obtain ⟨τ,hτ,hUse⟩ := cms_regularization_deficit_simple_second_away_from_first α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro m D d W a b n hSize hd hDens hDegree hNo hPair hOrder hStar hSimple hBase hBudget hLocal hRob
  exact hN D d hSize hd hDens hDegree hNo hPair hOrder hStar
    (fun v _ => hSimple v) hBase hBudget hLocal hRob

end OverfullWork.CanonicalRegularization
