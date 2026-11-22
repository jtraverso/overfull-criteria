module

public import ShannonColouring.Shannon

@[expose] public section


/-! # Multifans with labelled parallel copies: rotation

Fan vertices are distinct, while every spoke names its actual edge
copy. Rotation recolors the last spoke and recurses to its predecessor;
it never identifies parallel copies with the same endpoint pair.
-/
namespace OverfullWork.CopyMultifan
open Finset ShannonColouring
open scoped Classical
variable {V I : Type*} [DecidableEq V] [DecidableEq I]
variable {ends : I → V × V} {s : Finset I} {k : ℕ} {c : I → Fin k}
variable {x : V} {e : I} {L : ℕ} {y : ℕ → V} {g : ℕ → I}
set_option maxHeartbeats 10000000

def Joins (ends : I → V × V) (e : I) (x y : V) : Prop := s((ends e).1,(ends e).2)=s(x,y)

theorem Joins.incident_iff {h : I} {a b v : V} (hj : Joins ends h a b) :
    Incident ends h v ↔ v=a ∨ v=b := by
  have hh := congrArg (fun t : Sym2 V => v ∈ t) hj
  simpa only [Sym2.mem_iff,Incident,eq_comm] using Iff.of_eq hh

theorem Joins.other_unique {h : I} {a b z : V} (hb : Joins ends h a b) (hz : Joins ends h a z) : b=z := by
  have hh : s(a,b)=s(a,z) := hb.symm.trans hz
  rcases Sym2.eq_iff.mp hh with h|h
  · exact h.2
  · exact h.2.trans h.1

theorem Joins.ne (hloop : ∀ h, (ends h).1 ≠ (ends h).2) {h : I} {a b : V}
    (hj : Joins ends h a b) : a ≠ b := by
  intro hab
  have hd : (s((ends h).1,(ends h).2) : Sym2 V).IsDiag := by rw [hj,hab];simp
  exact hloop h (Sym2.mk_isDiag_iff.mp hd)

theorem misses_update_of_not_incident {h : I} {v : V} {a b : Fin k}
    (hv : ¬Incident ends h v) (hm : Misses ends s c v a) :
    Misses ends s (Function.update c h b) v a := by
  intro j hj hjv
  have hne : j ≠ h := fun he => hv (he ▸ hjv)
  rw [Function.update_of_ne hne]
  exact hm j hj hjv

theorem ProperOn.extend_joins (hc : ProperOn ends s c) (he : e ∉ s) {z : V}
    (hj : Joins ends e x z) {a : Fin k} (hx : Misses ends s c x a) (hz : Misses ends s c z a) :
    ∃ c' : I → Fin k, ProperOn ends (insert e s) c' := by
  have hm : ∀ v, Incident ends e v → Misses ends s c v a := by
    intro v hv
    rcases hj.incident_iff.mp hv with rfl|rfl
    · exact hx
    · exact hz
  exact ⟨_,hc.extend he (hm _ (Or.inl rfl)) (hm _ (Or.inr rfl))⟩

structure IsFan (ends : I → V × V) (s : Finset I) (c : I → Fin k) (x : V) (e : I)
    (L : ℕ) (y : ℕ → V) (g : ℕ → I) : Prop where
  pos : 0 < L
  start : g 0=e
  joins : ∀ i, i < L → Joins ends (g i) x (y i)
  inj : ∀ i, i < L → ∀ j, j < L → y i=y j → i=j
  colored : ∀ i, 0 < i → i < L → g i ∈ s
  step : ∀ i, 0 < i → i < L → ∃ j, j < i ∧ Misses ends s c (y j) (c (g i))

theorem IsFan.prefix (hF : IsFan ends s c x e L y g) {m : ℕ} (hm : m ≤ L) (hm0 : 0 < m) :
    IsFan ends s c x e m y g :=
  ⟨hm0,hF.start,fun i hi => hF.joins i (by omega),
    fun i hi j hj hh => hF.inj i (by omega) j (by omega) hh,
    fun i hi0 hi => hF.colored i hi0 (by omega),fun i hi0 hi => hF.step i hi0 (by omega)⟩

theorem IsFan.spokes_ne (hF : IsFan ends s c x e L y g)
    {i j : ℕ} (hi : i < L) (hj : j < L) (hij : i ≠ j) : g i ≠ g j := by
  intro hh
  have hsame : Joins ends (g i) x (y j) := hh ▸ hF.joins j hj
  exact hij (hF.inj i hi j hj ((hF.joins i hi).other_unique hsame))

theorem IsFan.no_incident_earlier (hF : IsFan ends s c x e L y g)
    (hloop : ∀ h, (ends h).1 ≠ (ends h).2) {i j : ℕ}
    (hi : i < L) (hj : j < L) (hij : i ≠ j) : ¬Incident ends (g j) (y i) := by
  intro hh
  rcases (hF.joins j hj).incident_iff.mp hh with hh|hh
  · exact (hF.joins i hi).ne hloop hh.symm
  · exact hij (hF.inj i hi j hj hh)

theorem rotate (hloop : ∀ h, (ends h).1 ≠ (ends h).2) (he : e ∉ s) :
    ∀ q : ℕ, ∀ (c : I → Fin k) (L : ℕ), ProperOn ends s c → IsFan ends s c x e L y g →
      q < L → ∀ a : Fin k, Misses ends s c x a → Misses ends s c (y q) a →
        ∃ c' : I → Fin k, ProperOn ends (insert e s) c' := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro c L hc hF hq a hax haq
    by_cases hq0 : q=0
    · subst q
      have hj := hF.joins 0 hF.pos
      rw [hF.start] at hj
      exact ProperOn.extend_joins hc he hj hax haq
    have hqPos : 0 < q := by omega
    obtain ⟨j,hjq,hmiss⟩ := hF.step q hqPos hq
    let b := c (g q)
    have hqmem := hF.colored q hqPos hq
    have hqcentre : Incident ends (g q) x := (hF.joins q hq).incident_iff.mpr (Or.inl rfl)
    have hab : a ≠ b := fun hh => hax (g q) hqmem hqcentre hh.symm
    let c₁ := Function.update c (g q) a
    have hc₁ : ProperOn ends s c₁ := by
      apply hc.recolour hqmem
      intro v hv
      rcases (hF.joins q hq).incident_iff.mp hv with rfl|rfl
      · exact hax
      · exact haq
    have hprefix : IsFan ends s c₁ x e (j+1) y g := by
      refine ⟨by omega,hF.start,fun i hi => hF.joins i (by omega),
        fun i hi l hl hh => hF.inj i (by omega) l (by omega) hh,
        fun i hi0 hi => hF.colored i hi0 (by omega),?_⟩
      intro i hi0 hi
      obtain ⟨l,hli,hlmiss⟩ := hF.step i hi0 (by omega)
      refine ⟨l,hli,?_⟩
      have hgi : g i ≠ g q := hF.spokes_ne (by omega) hq (by omega)
      change Misses ends s c₁ (y l) (Function.update c (g q) a (g i))
      rw [Function.update_of_ne hgi]
      exact misses_update_of_not_incident (hF.no_incident_earlier hloop (by omega) hq (by omega)) hlmiss
    have hbx : Misses ends s c₁ x b := by
      intro t ht htx
      by_cases htq : t=g q
      · subst t
        change Function.update c (g q) a (g q) ≠ b
        rw [Function.update_self]
        exact hab
      · change Function.update c (g q) a t ≠ b
        rw [Function.update_of_ne htq]
        exact hc.ne_of_incident ht hqmem htq htx hqcentre
    have hbj : Misses ends s c₁ (y j) b :=
      misses_update_of_not_incident (hF.no_incident_earlier hloop (by omega) hq (by omega)) hmiss
    exact ih j hjq c₁ (j+1) hc₁ hprefix (by omega) b hbx hbj

theorem IsFan.not_common_root (hF : IsFan ends s c x e L y g)
    (hloop : ∀ h, (ends h).1 ≠ (ends h).2) (he : e ∉ s) (hc : ProperOn ends s c)
    (hNo : ¬∃ c' : I → Fin k, ProperOn ends (insert e s) c')
    {i : ℕ} (hi : i < L) {a : Fin k} (hx : Misses ends s c x a)
    (hy : Misses ends s c (y i) a) : False :=
  hNo (rotate hloop he i c L hc hF hi a hx hy)

end OverfullWork.CopyMultifan
