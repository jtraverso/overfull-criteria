module

public import OverfullWork.DirectedListRoutes
public import Mathlib.Data.List.Chain

@[expose] public section


/-! A directed graph with at most one entering and leaving arc at each
vertex and with arcs that strictly increase rank has one path per
terminal vertex. Isolated vertices contribute one singleton path. -/
namespace OverfullWork.RankedDirectedPathCover

open Finset
open scoped Classical
variable {V : Type*}

noncomputable def terminals (R : V → V → Prop) (S : Finset V) : Finset V :=
  S.filter fun x => ∀ y ∈ S, ¬ R x y

structure Cover (R : V → V → Prop) (S : Finset V) where
  path : V → List V
  chain : ∀ t ∈ terminals R S, (path t).IsChain R
  simple : ∀ t ∈ terminals R S, (path t).Nodup
  ends : ∀ t ∈ terminals R S, (path t).getLast? = some t
  inside : ∀ t ∈ terminals R S, ∀ x ∈ path t, x ∈ S
  covers : ∀ x ∈ S, ∃ t ∈ terminals R S, x ∈ path t
  disjoint : ∀ t ∈ terminals R S, ∀ s ∈ terminals R S, t ≠ s → List.Disjoint (path t) (path s)

private theorem begins_of_no_predecessor (R : V → V → Prop) (p : List V) (w : V)
    (hc : p.IsChain R) (hw : w ∈ p)
    (h : ∀ x ∈ p, ¬ R x w) : ∃ l, p = w :: l := by
  obtain ⟨a,b,rfl⟩ := List.mem_iff_append.mp hw
  cases a with
  | nil => exact ⟨b,rfl⟩
  | cons x a =>
    have hne : x :: a ≠ [] := by simp
    let y := (x :: a).getLast hne
    have hLast : (x :: a).getLast? = some y := List.getLast?_eq_some_getLast hne
    have hArc : R y w :=
      (List.isChain_append.mp hc).2.2 y (by simp [hLast]) w (by simp)
    exact False.elim (h y (List.mem_append_left _ (List.getLast_mem hne)) hArc)

/-- Construct the paths, indexed by their exact terminal set. The
induction removes a vertex of minimum rank and prepends it to the path
starting at its successor whenever that successor exists. -/
theorem exists_cover (R : V → V → Prop) (rank : V → ℕ)
    (hRank : ∀ {x y}, R x y → rank x < rank y)
    (hIn : ∀ {x y z}, R x z → R y z → x = y) (S : Finset V) :
    Nonempty (Cover R S) := by
  classical
  induction S using Finset.strongInductionOn
  rename_i S ih
  all_goals
    rcases S.eq_empty_or_nonempty with rfl|hne
    · exact ⟨⟨fun _ => [], by simp [terminals], by simp [terminals], by simp [terminals],
        by simp [terminals], by simp, by simp [terminals]⟩⟩
    obtain ⟨x,hx,hLeast⟩ := exists_min_image S rank hne
    let S' := S.erase x
    have hSub : S' ⊂ S := erase_ssubset hx
    obtain ⟨C⟩ := ih S' hSub
    have hx' : x ∉ S' := notMem_erase _ _
    have hOld : ∀ w, w ∈ S' ↔ w ≠ x ∧ w ∈ S := fun _ => mem_erase
    have hNo : ∀ w ∈ S, ¬R w x := fun w hw h => (not_lt_of_ge (hLeast w hw)) (hRank h)
    have hTerm : ∀ t, t ∈ terminals R S' ↔ t ∈ terminals R S ∧ t ≠ x := by
      intro t
      constructor
      · intro ht
        obtain ⟨ht',hn⟩ := mem_filter.mp ht
        refine ⟨mem_filter.mpr ⟨(hOld t).mp ht' |>.2, fun w hw he => ?_⟩, ((hOld t).mp ht').1⟩
        by_cases h : w = x
        · exact hNo t ((hOld t).mp ht').2 (h ▸ he)
        · exact hn w ((hOld w).mpr ⟨h,hw⟩) he
      · rintro ⟨ht,hn⟩
        obtain ⟨ht',he⟩ := mem_filter.mp ht
        exact mem_filter.mpr ⟨(hOld t).mpr ⟨hn,ht'⟩, fun w hw => he w ((hOld w).mp hw).2⟩
    by_cases hNext : ∃ w ∈ S, R x w
    · obtain ⟨w,hw,hArc⟩ := hNext
      have hxNot : x ∉ terminals R S := fun ht => (mem_filter.mp ht).2 w hw hArc
      have hT : ∀ t, t ∈ terminals R S ↔ t ∈ terminals R S' := by
        intro t
        rw [hTerm]
        exact ⟨fun ht => ⟨ht,fun he => hxNot (he ▸ ht)⟩, And.left⟩
      have hw' : w ∈ S' := (hOld w).mpr ⟨fun he => hNo x hx (he ▸ hArc),hw⟩
      obtain ⟨t,ht,hwt⟩ := C.covers w hw'
      have hPred : ∀ y ∈ C.path t, ¬R y w := by
        intro y hy he
        have h := hIn he hArc
        exact hx' (h ▸ C.inside t ht y hy)
      obtain ⟨l,hl⟩ := begins_of_no_predecessor R (C.path t) w (C.chain t ht) hwt hPred
      let p := Function.update C.path t (x :: C.path t)
      have hpMem : ∀ s v, v ∈ p s ↔ v ∈ C.path s ∨ s = t ∧ v = x := by
        intro s v
        by_cases he : s = t
        · subst s
          simp [p, or_comm]
        · simp [p, he]
      have hChain : (p t).IsChain R := by
        rw [show p t = x :: C.path t from Function.update_self ..,hl]
        apply List.IsChain.cons_cons hArc
        exact hl ▸ C.chain t ht
      have hSimple : (p t).Nodup := by
        rw [show p t = x :: C.path t from Function.update_self ..]
        exact List.nodup_cons.mpr ⟨fun h => hx' (C.inside t ht x h), C.simple t ht⟩
      refine ⟨⟨p,?_,?_,?_,?_,?_,?_⟩⟩
      · intro s hs
        by_cases he : s = t
        · exact he.symm ▸ hChain
        · simpa only [p, Function.update_of_ne he] using C.chain s ((hT s).mp hs)
      · intro s hs
        by_cases he : s = t
        · exact he.symm ▸ hSimple
        · simpa only [p, Function.update_of_ne he] using C.simple s ((hT s).mp hs)
      · intro s hs
        by_cases he : s = t
        · subst s
          rw [show p t = x :: C.path t from Function.update_self .., hl,
            List.getLast?_cons_cons, ← hl]
          exact C.ends t ht
        · simpa only [p, Function.update_of_ne he] using C.ends s ((hT s).mp hs)
      · intro s hs v hv
        rcases (hpMem s v).mp hv with hv|⟨_,rfl⟩
        · exact (hOld v).mp (C.inside s ((hT s).mp hs) v hv) |>.2
        · exact hx
      · intro v hv
        by_cases he : v = x
        · exact ⟨t,(hT t).mpr ht,(hpMem t v).mpr (Or.inr ⟨rfl,he⟩)⟩
        · obtain ⟨s,hs,hv'⟩ := C.covers v ((hOld v).mpr ⟨he,hv⟩)
          exact ⟨s,(hT s).mpr hs,(hpMem s v).mpr (Or.inl hv')⟩
      · intro s hs u hu hsu v hv hv'
        have hs' := (hT s).mp hs
        have hu' := (hT u).mp hu
        rcases (hpMem s v).mp hv with hv|⟨hst,hvx⟩
        · rcases (hpMem u v).mp hv' with hv'|⟨_,hvx⟩
          · exact C.disjoint s hs' u hu' hsu hv hv'
          · subst v
            exact hx' (C.inside s hs' x hv)
        · subst v
          rcases (hpMem u x).mp hv' with hv'|⟨hut,_⟩
          · exact hx' (C.inside u hu' x hv')
          · exact hsu (hst.trans hut.symm)
    · have hxT : x ∈ terminals R S := mem_filter.mpr ⟨hx,fun y hy hr => hNext ⟨y,hy,hr⟩⟩
      let p := Function.update C.path x [x]
      have hUpdate : p x = [x] := Function.update_self ..
      have hKeep : ∀ t, t ≠ x → p t = C.path t := fun _ ht => Function.update_of_ne ht ..
      refine ⟨⟨p,?_,?_,?_,?_,?_,?_⟩⟩
      · intro t ht
        by_cases h : t = x
        · subst t; rw [hUpdate]; exact .singleton _
        · rw [hKeep t h]; exact C.chain t ((hTerm t).mpr ⟨ht,h⟩)
      · intro t ht
        by_cases h : t = x
        · subst t; simp [hUpdate]
        · rw [hKeep t h]; exact C.simple t ((hTerm t).mpr ⟨ht,h⟩)
      · intro t ht
        by_cases h : t = x
        · subst t; simp [hUpdate]
        · rw [hKeep t h]; exact C.ends t ((hTerm t).mpr ⟨ht,h⟩)
      · intro t ht v hv
        by_cases h : t = x
        · subst t
          rw [hUpdate] at hv
          exact (List.mem_singleton.mp hv).symm ▸ hx
        · rw [hKeep t h] at hv
          exact (hOld v).mp (C.inside t ((hTerm t).mpr ⟨ht,h⟩) v hv) |>.2
      · intro v hv
        by_cases h : v = x
        · subst v; exact ⟨x,hxT,by simp [hUpdate]⟩
        · obtain ⟨t,ht,hv'⟩ := C.covers v ((hOld v).mpr ⟨h,hv⟩)
          obtain ⟨ht',htx⟩ := (hTerm t).mp ht
          exact ⟨t,ht',by rw [hKeep t htx]; exact hv'⟩
      · intro t ht s hs hts v hv hv'
        by_cases h : t = x
        · subst t
          rw [hUpdate] at hv
          have hvx := List.mem_singleton.mp hv
          subst v
          rw [hKeep s hts.symm] at hv'
          exact hx' (C.inside s ((hTerm s).mpr ⟨hs,hts.symm⟩) x hv')
        · by_cases h' : s = x
          · subst s
            rw [hUpdate] at hv'
            have hvx := List.mem_singleton.mp hv'
            subst v
            rw [hKeep t h] at hv
            exact hx' (C.inside t ((hTerm t).mpr ⟨ht,h⟩) x hv)
          · rw [hKeep t h] at hv
            rw [hKeep s h'] at hv'
            exact C.disjoint t ((hTerm t).mpr ⟨ht,h⟩) s ((hTerm s).mpr ⟨hs,h'⟩) hts hv hv'

/-- When leaving arcs are also unique, every arc on the covered
vertex set occurs in its path. -/
theorem Cover.arc_occurs {R : V → V → Prop} {S : Finset V} (C : Cover R S)
    (hOut : ∀ {x y z}, R x y → R x z → y = z) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hArc : R x y) :
    ∃ t ∈ terminals R S, List.IsInfix [x,y] (C.path t) := by
  obtain ⟨t,ht,hm⟩ := C.covers x hx
  obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hm
  cases B with
  | nil =>
    have he := C.ends t ht
    rw [hAB, List.getLast?_append_of_ne_nil A (by simp)] at he
    have hxt : x = t := Option.some.inj he
    have hxt' : x ∈ terminals R S := hxt.symm ▸ ht
    exact False.elim ((mem_filter.mp hxt').2 y hy hArc)
  | cons z B =>
    have hList := C.chain t ht
    rw [hAB] at hList
    have hEdge := (List.isChain_split.mp hList).2.rel
    have he : y = z := hOut hArc hEdge
    subst z
    exact ⟨t,ht,A,B,by simpa only [List.append_assoc,List.cons_append,List.nil_append] using hAB.symm⟩

end OverfullWork.RankedDirectedPathCover
