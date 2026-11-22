module

public import OverfullWork.OsthusStadenShadowBalance

@[expose] public section


/-! Turn the spacing of the original red clusters into the disjoint
black cuts used in Osthus–Staden §5.11. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {U : Type*}

noncomputable def shadowShift (incoming outgoing : Finset U) (a : ↥(incoming ∪ outgoing)) : ℕ :=
  if (a:U) ∈ incoming then 1 else 0

theorem pow_shadowSend (σ : Equiv.Perm U) (incoming outgoing : Finset U)
    (a : ↥(incoming ∪ outgoing)) :
    (σ^(shadowShift incoming outgoing a)) (shadowSend σ incoming outgoing a) = a := by
  by_cases h : (a:U) ∈ incoming <;> simp [shadowShift,shadowSend,h]

/-- Moving each red cluster back by at most one step reduces the
spacing bound by at most one. The two orientations become consecutive
pairs starting at the shadow sources. -/
theorem shadow_starts_spaced (σ : Equiv.Perm U) (incoming outgoing : Finset U) (p : ℕ)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:U) = (b:U) → p ≤ j) :
    ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (shadowSend σ incoming outgoing a) = shadowSend σ incoming outgoing b → p-1 ≤ j := by
  intro a b j hj h
  let u := shadowSend σ incoming outgoing a
  let v := shadowSend σ incoming outgoing b
  let s := shadowShift incoming outgoing a
  let t := shadowShift incoming outgoing b
  have hs : s ≤ 1 := by simp [s,shadowShift]; split <;> omega
  have ht : t ≤ 1 := by simp [t,shadowShift]; split <;> omega
  have hsu : (σ^s) u = (a:U) := pow_shadowSend σ incoming outgoing a
  have htv : (σ^t) v = (b:U) := pow_shadowSend σ incoming outgoing b
  have htu : (σ^(t+j)) u = (b:U) := by
    rw [pow_add,Equiv.Perm.mul_apply,show (σ^j) u = v from h,htv]
  have hStrict : s < t+j := by
    by_contra! h'
    have he : s = t+j := by omega
    have hab : a = b := Subtype.ext (by rw [←hsu,he,htu])
    have hst : s = t := congrArg (shadowShift incoming outgoing) hab
    omega
  have hPos : 0 < t+j-s := by omega
  have hPow : (σ^(t+j-s)) (a:U) = (b:U) := by
    rw [←hsu,←Equiv.Perm.mul_apply,←pow_add,show t+j-s+s = t+j by omega,htu]
  have hLower := hSpacing a b (t+j-s) hPos hPow
  omega

/-- A black cluster is neither the first nor the second cluster
of a consecutive red pair. -/
def IsBlackAfterBalancing (σ : Equiv.Perm U) (incoming outgoing : Finset U) (x : U) : Prop :=
  x ∉ Set.range (shadowSend σ incoming outgoing) ∧ x ∉ Set.range (shadowReceive σ incoming outgoing)

/-- The offsets `2, …, p−2` give at least `p−3` consecutive black
clusters after every consecutive red pair. -/
theorem black_after_red_pair (σ : Equiv.Perm U) (incoming outgoing : Finset U) (p : ℕ)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:U) = (b:U) → p ≤ j)
    (a : ↥(incoming ∪ outgoing)) (j : ℕ) (hlo : 2 ≤ j) (hhi : j < p-1) :
    IsBlackAfterBalancing σ incoming outgoing ((σ^j) (shadowSend σ incoming outgoing a)) := by
  have h := shadow_starts_spaced σ incoming outgoing p hSpacing
  constructor
  · rintro ⟨b,hb⟩
    exact (not_le_of_gt hhi) (h a b j (by omega) hb.symm)
  · rintro ⟨b,hb⟩
    have h' : (σ^(j-1)) (shadowSend σ incoming outgoing a) = shadowSend σ incoming outgoing b := by
      apply σ.injective
      simpa only [shadowReceive,←Equiv.Perm.mul_apply,←pow_succ',show (j-1)+1 = j by omega] using hb.symm
    exact (not_le_of_gt (show j-1 < p-1 by omega)) (h a b (j-1) (by omega) h')

/-- Each of the `p−4` offsets chooses one outgoing black arc after
each red pair. Sources of cuts are distinct across all offsets and pairs. -/
theorem black_cut_sources_injective (σ : Equiv.Perm U) (incoming outgoing : Finset U) (p : ℕ)
    (hSep : ∀ u ∈ outgoing, σ u ∉ incoming)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:U) = (b:U) → p ≤ j) :
    Function.Injective (fun x : ↥(incoming ∪ outgoing) × Fin (p-4) =>
      (σ^(2+x.2.val)) (shadowSend σ incoming outgoing x.1)) := by
  let S := shadowSend σ incoming outgoing
  have hS := shadowSend_injective σ incoming outgoing hSep
  have h := shadow_starts_spaced σ incoming outgoing p hSpacing
  have hdiff (a b : ↥(incoming ∪ outgoing)) (q r : Fin (p-4))
      (hl : q.val < r.val) (he : (σ^(2+q.val)) (S a) = (σ^(2+r.val)) (S b)) : False := by
    have hStep : (σ^(r.val-q.val)) (S b) = S a := by
      apply (σ^(2+q.val)).injective
      rw [←Equiv.Perm.mul_apply,←pow_add,show 2+q.val+(r.val-q.val) = 2+r.val by omega]
      exact he.symm
    have hBound := h b a (r.val-q.val) (by omega) hStep
    have := r.isLt
    omega
  rintro ⟨a,q⟩ ⟨b,r⟩ he
  change (σ^(2+q.val)) (S a) = (σ^(2+r.val)) (S b) at he
  rcases lt_trichotomy q.val r.val with hl | hl | hl
  · exact (hdiff a b q r hl he).elim
  · have hr : q = r := Fin.ext hl
    subst r
    exact Prod.ext (hS ((σ^(2+q.val)).injective he)) rfl
  · exact (hdiff b a r q hl he.symm).elim

/-- The predecessor of a red pair is black when the original red
clusters have spacing at least four. -/
theorem black_before_red_pair (σ : Equiv.Perm U) (incoming outgoing : Finset U) (p : ℕ)
    (hp : 4 ≤ p)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) j, 0 < j →
      (σ^j) (a:U) = (b:U) → p ≤ j)
    (a : ↥(incoming ∪ outgoing)) :
    IsBlackAfterBalancing σ incoming outgoing (σ.symm (shadowSend σ incoming outgoing a)) := by
  have h := shadow_starts_spaced σ incoming outgoing p hSpacing
  constructor
  · rintro ⟨b,hb⟩
    have he := congrArg σ hb
    rw [σ.apply_symm_apply] at he
    have h1 := h b a 1 (by decide) (by simpa only [pow_one] using he)
    omega
  · rintro ⟨b,hb⟩
    have he := congrArg σ hb
    rw [σ.apply_symm_apply] at he
    have h2 := h b a 2 (by decide) (by simpa only [shadowReceive,pow_two,Equiv.Perm.mul_apply] using he)
    omega

end OverfullWork.DirectedRobustExpansion
