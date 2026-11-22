module

public import OverfullWork.CMSOperation41OriginalPhaseReserves
public import OverfullWork.CMSOperation41CleanedSelection

@[expose] public section


/-! A prefix before the first critical change of active vertices.
The graph records and the degree records advance together, and each
selection retains the data needed for later physical packing. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def HasStoredOriginalTrimmingSelection (initial low exceptional : Finset V)
    (S T P : SimpleGraph V) (degree credit : V → ℕ) (special : Option V)
    (internal : V → Prop) (free : Finset V) (d floor j cap : ℕ) : Prop :=
  let cleanDegree := fun v => degree v-(sdiff S T).degree v
  let support := univ.filter (fun v => 0 < cleanDegree v)
  ∃ used : ℕ → Finset V,
    ∃ R : TrimmingStepSelection T initial (exceptional ∩ support)
      (originalCleanActive low exceptional T) cleanDegree d floor used j cap,
      P = R.round.words.prescribedGraph ∧ credit = R.round.words.degreeCredit R.round.omitted ∧
      special = R.special ∧ internal = R.internalCharge ∧
      ∀ e,let v := (R.round.words.endpoint e).val
        v ∈ free ∨ (∃ w ∈ originalCleanActive low exceptional T,P.Adj w v) ∨ 0 < credit v

structure OriginalTrimmingHistory (G : SimpleGraph V) [DecidableRel G.Adj]
    (initial low : Finset V) (threshold floor cap test m : ℕ) where
  graph : ℕ → SimpleGraph V
  cleaned : ℕ → SimpleGraph V
  prescribed : ℕ → SimpleGraph V
  exceptional : ℕ → Finset V
  degree : ℕ → V → ℕ
  credit : ℕ → V → ℕ
  special : ℕ → Option V
  internal : ℕ → V → Prop
  free : ℕ → Finset V
  graph_zero : graph 0 = G
  exceptional_zero : exceptional 0 = initial
  degree_zero : degree 0 = fun v => G.degree v
  degree_exact : ∀ i ≤ m,degree i = auxiliaryPhysicalDegree (graph i) initial prescribed credit i
  degree_bound : ∀ i ≤ m,∀ v,degree i v ≤ G.maxDegree-2*i
  cleanup : ∀ i < m,DeletionRun (exceptional i ∩ low) (graph i) (cleaned i)
  graph_next : ∀ i < m,graph (i+1) = sdiff (cleaned i) (prescribed i)
  degree_next : ∀ i < m,∀ v,
    degree (i+1) v+(sdiff (graph i) (cleaned i)).degree v+(2-credit i v) = degree i v
  exceptional_next : ∀ i < m,exceptional (i+1) = nextTrimmingExceptional (exceptional i)
    (univ.filter (fun v => 0 < degree (i+1) v)) (degree (i+1)) (G.maxDegree-2*(i+1)) threshold
  no_stop : ∀ i < m,¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < degree i v))
    (G.maxDegree-2*i) test (degree i)
  free_size : ∀ i < m,(free i).card ≤ 2*(initial.card+1)
  free_load : ∀ v,projectionLoad (range m) free v ≤ cap
  selection : ∀ i < m,HasStoredOriginalTrimmingSelection initial low (exceptional i)
    (graph i) (cleaned i) (prescribed i) (degree i) (credit i) (special i)
    (internal i) (free i) (G.maxDegree-2*i) floor i cap

theorem original_trimming_history_zero (G : SimpleGraph V) [dG : DecidableRel G.Adj]
    (initial low : Finset V) (threshold floor cap test : ℕ) :
    Nonempty (OriginalTrimmingHistory G initial low threshold floor cap test 0) := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  refine ⟨{
    graph := fun _ => G
    cleaned := fun _ => G
    prescribed := fun _ => ⊥
    exceptional := fun _ => initial
    degree := fun _ v => G.degree v
    credit := fun _ _ => 2
    special := fun _ => none
    internal := fun _ _ => False
    free := fun _ => ∅
    graph_zero := rfl
    exceptional_zero := rfl
    degree_zero := rfl
    degree_exact := ?_
    degree_bound := fun i hi v => by
      have he : i = 0 := by omega
      subst i
      simpa using G.degree_le_maxDegree v
    cleanup := by simp
    graph_next := by simp
    degree_next := by simp
    exceptional_next := by simp
    no_stop := by simp
    free_size := by simp
    free_load := by simp [projectionLoad]
    selection := by simp }⟩
  intro i hi
  have he : i = 0 := by omega
  subst i
  funext v
  simp [auxiliaryPhysicalDegree]

set_option maxHeartbeats 2500000 in
/-- Reconstruct the inequalities for the next selector entirely
from the saved prefix and the original scale assumptions. -/
theorem OriginalTrimmingHistory.next_round_reserves
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test m : ℕ}
    (H : OriginalTrimmingHistory G initial low threshold floor cap test m)
    (hLow : low ⊆ initial) (hInd : G.IsIndepSet (low : Set V))
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+threshold)
    (hFloor : ∀ v ∈ initial,v ∉ low → floor ≤ G.degree v)
    (hMargin : 5*initial.card+cap+4+(4*initial.card+2) ≤ floor)
    (hRange : floor+threshold+low.card ≤ G.maxDegree-2*m) :
    (∀ v,v ∉ initial → (H.exceptional m ∩ low).card+2 ≤ H.degree m v) ∧
    ∀ v ∈ initial,v ∉ H.exceptional m ∩ low → 0 < (H.graph m).degree v →
      5*initial.card+cap+4+(H.exceptional m ∩ low).card ≤ (H.graph m).degree v ∧
      floor ≤ (H.graph m).degree v+2*low.card+initial.card+1 := by
  let U := H.exceptional
  have hU (i : ℕ) (hi : i ≤ m) : U i ⊆ initial :=
    H.exceptional_zero ▸ trimming_exceptional_sets_antitone U
      (fun k => univ.filter (fun v => 0 < H.degree k v)) H.degree G.maxDegree threshold m
      H.exceptional_next i hi 0 (Nat.zero_le _)
  have hLayer (i : ℕ) (hi : i < m) : H.prescribed i ≤ H.cleaned i := by
    obtain ⟨_,R,hP,_,_,_,_⟩ := H.selection i hi
    rw [hP]
    exact R.round.words.prescribedGraph_le
  refine original_phase_next_round_reserves G initial low hLow H.graph H.cleaned H.prescribed U
    H.degree H.credit H.special H.internal m threshold floor cap
    H.graph_zero H.exceptional_zero H.degree_zero hInd H.cleanup hLayer H.graph_next
    H.exceptional_next H.degree_next ?_ hOrd hFloor ?_ ?_ ?_ hMargin hRange
  · intro v hv
    rw [H.degree_exact m le_rfl,auxiliaryPhysicalDegree,if_pos hv]
  · intro i hi v hs
    obtain ⟨_,R,hP,_,hSpecial,_,_⟩ := H.selection i hi
    rw [hSpecial] at hs
    obtain ⟨hv,hHigh,hTwo⟩ := R.special_debit v hs
    have hvI := hU i hi.le (mem_inter.mp hv).1
    have hRecord : H.degree i v = (H.graph i).degree v := by
      rw [H.degree_exact i hi.le,auxiliaryPhysicalDegree,if_pos hvI]
    rw [hP]
    change floor+2 ≤ H.degree i v-(sdiff (H.graph i) (H.cleaned i)).degree v at hHigh
    omega
  · intro i hi v hint
    obtain ⟨_,R,hP,_,_,hInternal,_⟩ := H.selection i hi
    rw [hInternal] at hint
    obtain ⟨w,hw,_,hSmall,hOne,_⟩ := hint
    rw [hP]
    exact ⟨w,hw,hSmall.trans_le (Nat.add_le_add_right (card_le_card inter_subset_left) _),hOne.ge⟩
  · intro i hi v hv hLowV hp
    obtain ⟨_,R,hP,_,hSpecial,hInternal,_⟩ := H.selection i hi
    have hRecord : H.degree i v = (H.graph i).degree v := by
      rw [H.degree_exact i hi.le,auxiliaryPhysicalDegree,if_pos (hU i hi.le hv)]
    have hCleanRecord : H.degree i v-(sdiff (H.graph i) (H.cleaned i)).degree v =
        (H.cleaned i).degree v := by
      have h := auxiliary_physical_degree_after_cleanup (H.graph i) (H.cleaned i) initial
        H.prescribed H.credit i (DeletionRun.le_source (H.cleanup i hi)) v
      rw [auxiliaryPhysicalDegree,if_pos (hU i hi.le hv),←H.degree_exact i hi.le] at h
      exact h.symm
    have hvR : v ∈ H.exceptional i ∩
        univ.filter (fun x => 0 < H.degree i x-(sdiff (H.graph i) (H.cleaned i)).degree x) :=
      mem_inter.mpr ⟨hv,mem_filter.mpr ⟨mem_univ _,by rwa [hCleanRecord]⟩⟩
    rw [hP,hSpecial,hInternal]
    apply R.exceptional_cost (H.graph i) low hvR (inter_subset_left.trans (hU i hi.le))
      (fun h => hLowV ((mem_inter.mp (mem_filter.mp h).1).2))
      (fun _ h => (mem_inter.mp (mem_filter.mp h).1).2)
    intro x hx
    exact (mem_inter.mp ((cleanup_removed_edge_meets_active (H.cleanup i hi) hx).resolve_left
      (fun h => hLowV (mem_inter.mp h).2))).2

set_option maxHeartbeats 3600000 in
/-- Append a real selection to the virtual prefix and retain its
prescribed words and exact credit for the eventual packing. -/
theorem OriginalTrimmingHistory.snoc
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test m : ℕ}
    (H : OriginalTrimmingHistory G initial low threshold floor cap test m)
    (T : SimpleGraph V) (hRun : DeletionRun (H.exceptional m ∩ low) (H.graph m) T)
    (hStop : ¬HasAlmostOverfullRecord (univ.filter (fun v => 0 < H.degree m v))
      (G.maxDegree-2*m) test (H.degree m))
    (hCore : ∀ v,v ∉ initial → 2 ≤ H.degree m v-(sdiff (H.graph m) T).degree v)
    (hAdd : ∀ v,(H.degree m v-(sdiff (H.graph m) T).degree v)+
      (sdiff (H.graph m) T).degree v = H.degree m v)
    (R : TrimmingStepSelection T initial
      (H.exceptional m ∩ univ.filter (fun v => 0 < H.degree m v-(sdiff (H.graph m) T).degree v))
      (originalCleanActive low (H.exceptional m) T)
      (fun v => H.degree m v-(sdiff (H.graph m) T).degree v)
      (G.maxDegree-2*m) floor H.free m cap) :
    Nonempty (OriginalTrimmingHistory G initial low threshold floor cap test (m+1)) := by
  let D := G.maxDegree
  let C := sdiff (H.graph m) T
  let P := R.round.words.prescribedGraph
  let credit := R.round.words.degreeCredit R.round.omitted
  let next := sdiff T P
  let record (v : V) := (H.degree m v-C.degree v)-(2-credit v)
  let current := nextTrimmingExceptional (H.exceptional m)
    (univ.filter (fun v => 0 < record v)) record (D-2*(m+1)) threshold
  let S' := Function.update H.graph (m+1) next
  let T' := Function.update H.cleaned m T
  let P' := Function.update H.prescribed m P
  let U' := Function.update H.exceptional (m+1) current
  let d' := Function.update H.degree (m+1) record
  let c' := Function.update H.credit m credit
  let s' := Function.update H.special m R.special
  let in' := Function.update H.internal m R.internalCharge
  let ends := univ.image (fun e => (R.round.words.endpoint e).val)
  let free := ends.filter (fun v => projectionLoad (range m) H.free v < cap)
  let f' := Function.update H.free m free
  obtain ⟨hSize,hFree,hLoad,hEnds⟩ := R.append_free_projections H.free_load
  change free.card ≤ 2*(initial.card+1) at hSize
  change ∀ i < m,f' i = H.free i at hFree
  change ∀ v,projectionLoad (range (m+1)) f' v ≤ cap at hLoad
  have hS (i : ℕ) (hi : i ≤ m) : S' i = H.graph i := Function.update_of_ne (by omega) _ _
  have hU (i : ℕ) (hi : i ≤ m) : U' i = H.exceptional i := Function.update_of_ne (by omega) _ _
  have hD (i : ℕ) (hi : i ≤ m) : d' i = H.degree i := Function.update_of_ne (by omega) _ _
  have hT (i : ℕ) (hi : i < m) : T' i = H.cleaned i := Function.update_of_ne hi.ne _ _
  have hP (i : ℕ) (hi : i < m) : P' i = H.prescribed i := Function.update_of_ne hi.ne _ _
  have hCredit (i : ℕ) (hi : i < m) : c' i = H.credit i := Function.update_of_ne hi.ne _ _
  have hSpecial (i : ℕ) (hi : i < m) : s' i = H.special i := Function.update_of_ne hi.ne _ _
  have hInternal (i : ℕ) (hi : i < m) : in' i = H.internal i := Function.update_of_ne hi.ne _ _
  have hmT : T' m = T := Function.update_self _ _ _
  have hmP : P' m = P := Function.update_self _ _ _
  have hmC : c' m = credit := Function.update_self _ _ _
  have hmF : f' m = free := Function.update_self _ _ _
  have hmS : S' (m+1) = next := Function.update_self _ _ _
  have hmU : U' (m+1) = current := Function.update_self _ _ _
  have hmD : d' (m+1) = record := Function.update_self _ _ _
  have hPrev (i : ℕ) (hi : i ≤ m) (v : V) :
      auxiliaryPhysicalDegree (H.graph i) initial P' c' i v = H.degree i v := by
    rw [H.degree_exact i hi]
    unfold auxiliaryPhysicalDegree
    split
    · rfl
    · congr 1
      apply sum_congr rfl
      intro j _
      rw [hP j (j.isLt.trans_le hi),hCredit j (j.isLt.trans_le hi)]
  have hDouble : sdiff (H.graph m) C = T := by
    ext a b
    have hLe := @DeletionRun.le_source _ _ _ _ _ _ hRun a b
    change ((H.graph m).Adj a b ∧ ¬((H.graph m).Adj a b ∧ ¬T.Adj a b)) ↔ T.Adj a b
    tauto
  have hVirtual (v : V) : auxiliaryPhysicalDegree next initial P' c' (m+1) v = record v := by
    have hp : P' m ≤ sdiff (H.graph m) C := by
      rw [hmP,hDouble]
      exact R.round.words.prescribedGraph_le
    have hc (w : V) (hw : w ∉ initial) : (P' m).degree w ≤ 2-c' m w := by
      rw [hmP,hmC]
      exact R.round.words.prescribed_degree_le_core_debit R.round.omitted R.round.endpoints_retained hw
    have h := auxiliary_physical_degree_after_round (H.graph m) C initial P' c' m
      (fun _ _ he => he.1) hp hc v
    dsimp only at h
    rw [hDouble,hmP,hmC,hPrev m le_rfl] at h
    by_cases hv : v ∈ initial
    · have he := R.round.words.prescribed_degree_add_credit_on_exceptional R.round.omitted hv
      change P.degree v+credit v = 2 at he
      rw [if_pos hv,show P.degree v = 2-credit v by omega,←Nat.sub_sub] at h
      exact h
    · rw [if_neg hv,←Nat.sub_sub] at h
      exact h
  have hRecord (v : V) : record v ≤ D-2*(m+1) ∧
      record v+C.degree v+(2-credit v) = H.degree m v := by
    have hCap := R.round.degree_cap v
    change H.degree m v-C.degree v+credit v ≤ D-2*m at hCap
    have hCan : 2-credit v ≤ H.degree m v-C.degree v := by
      by_cases hv : v ∈ initial
      · have hBal := R.round.words.prescribed_degree_add_credit_on_exceptional R.round.omitted hv
        have hPres : P.degree v ≤ T.degree v := degree_le_of_le R.round.words.prescribedGraph_le
        have hRead := auxiliary_physical_degree_after_cleanup (H.graph m) T initial
          H.prescribed H.credit m (DeletionRun.le_source hRun) v
        rw [auxiliaryPhysicalDegree,if_pos hv,←H.degree_exact m le_rfl] at hRead
        change T.degree v = H.degree m v-C.degree v at hRead
        change P.degree v+credit v = 2 at hBal
        omega
      · have h := hCore v hv
        change 2 ≤ H.degree m v-C.degree v at h
        omega
    have h := hAdd v
    change (H.degree m v-C.degree v)+C.degree v = H.degree m v at h
    dsimp only [record]
    omega
  refine ⟨⟨S',T',P',U',d',c',s',in',f',?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hLoad,?_⟩⟩
  · rw [hS 0 (Nat.zero_le _),H.graph_zero]
  · rw [hU 0 (Nat.zero_le _),H.exceptional_zero]
  · rw [hD 0 (Nat.zero_le _),H.degree_zero]
  · intro i hi
    by_cases he : i = m+1
    · subst i
      rw [hmD,hmS]
      exact funext fun v => (hVirtual v).symm
    · have hle : i ≤ m := by omega
      rw [hD i hle,hS i hle]
      exact funext fun v => (hPrev i hle v).symm
  · intro i hi v
    by_cases he : i = m+1
    · subst i
      rw [hmD]
      exact (hRecord v).1
    · have hle : i ≤ m := by omega
      rw [hD i hle]
      exact H.degree_bound i hle v
  · intro i hi
    by_cases he : i = m
    · subst i
      rw [hmT,hS m le_rfl,hU m le_rfl]
      exact hRun
    · have hlt : i < m := by omega
      rw [hT i hlt,hS i hlt.le,hU i hlt.le]
      exact H.cleanup i hlt
  · intro i hi
    by_cases he : i = m
    · subst i
      rw [hmS,hmT,hmP]
    · have hlt : i < m := by omega
      rw [hS (i+1) (by omega),hT i hlt,hP i hlt]
      exact H.graph_next i hlt
  · intro i hi v
    by_cases he : i = m
    · subst i
      rw [hmD,hmT,hmC,hD m le_rfl,hS m le_rfl]
      exact (hRecord v).2
    · have hlt : i < m := by omega
      rw [hD (i+1) (by omega),hS i hlt.le,hT i hlt,hCredit i hlt,hD i hlt.le]
      exact H.degree_next i hlt v
  · intro i hi
    by_cases he : i = m
    · subst i
      rw [hmU,hmD,hU m le_rfl]
    · have hlt : i < m := by omega
      rw [hU (i+1) (by omega),hD (i+1) (by omega),hU i hlt.le]
      exact H.exceptional_next i hlt
  · intro i hi
    by_cases he : i = m
    · subst i
      rw [hD m le_rfl]
      exact hStop
    · have hlt : i < m := by omega
      rw [hD i hlt.le]
      exact H.no_stop i hlt
  · intro i hi
    by_cases he : i = m
    · subst i
      rwa [hmF]
    · have hlt : i < m := by omega
      rw [hFree i hlt]
      exact H.free_size i hlt
  · intro i hi
    by_cases he : i = m
    · subst i
      rw [hmT,hmP,hmC,hmF,hD m le_rfl,hU m le_rfl,hS m le_rfl]
      simp only [s',in',Function.update_self]
      exact ⟨H.free,R,rfl,rfl,rfl,rfl,fun e =>
        hEnds _ (mem_image.mpr ⟨e,mem_univ _,rfl⟩)⟩
    · have hlt : i < m := by omega
      simpa only [hD i hlt.le,hS i hlt.le,hT i hlt,hU i hlt.le,hP i hlt,hCredit i hlt,
        hSpecial i hlt,hInternal i hlt,hFree i hlt] using H.selection i hlt

/-- Three exits from the original phase: its round limit, an
almost-overfull record, or the first critical active choice. The last
two can be detected immediately after the actual cleanup of the state. -/
def OriginalTrimmingHistory.AtBoundary
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test m : ℕ}
    (H : OriginalTrimmingHistory G initial low threshold floor cap test m) (limit : ℕ) : Prop :=
  let d := G.maxDegree-2*m
  m = limit ∨ HasAlmostOverfullRecord (univ.filter (fun v => 0 < H.degree m v)) d test (H.degree m) ∨
    ∃ T : SimpleGraph V,
      let cleaned := auxiliaryPhysicalDegree T initial H.prescribed H.credit m
      let support := univ.filter (fun v => 0 < cleaned v)
      let U := H.exceptional m ∩ support
      DeletionRun (H.exceptional m ∩ low) (H.graph m) T ∧
        (HasAlmostOverfullRecord support d test cleaned ∨
          (originalCleanActive low (H.exceptional m) T = ∅ ∧
            ∃ A ⊆ U,1 ≤ A.card ∧ A.card ≤ 2 ∧ (Even support.card ↔ A.card = 2) ∧
              (∀ z ∈ U,cleaned z < floor+2) ∧ Odd (support \ U).card ∧
              (∑ v ∈ support \ U,(d-cleaned v)) ≤ 1 ∧
              ((Even U.card ∧ ∃ a ∈ U,A = {a} ∧ ∀ v ∈ U,cleaned a ≤ cleaned v) ∨
                (Odd U.card ∧ ∃ a ∈ U,∃ b ∈ U,a ≠ b ∧ A = {a,b} ∧
                  (∀ v ∈ U,cleaned a ≤ cleaned v) ∧ ∀ v ∈ U,v ≠ a → cleaned b ≤ cleaned v))))

set_option maxHeartbeats 3600000 in
theorem OriginalTrimmingHistory.continue_or_boundary
    {G : SimpleGraph V} [dG : DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test m : ℕ}
    (H : OriginalTrimmingHistory G initial low threshold floor cap test m) (limit : ℕ)
    (hLow : low ⊆ initial) (hInd : G.IsIndepSet (low : Set V))
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+threshold)
    (hFloor : ∀ v ∈ initial,v ∉ low → floor ≤ G.degree v)
    (hDef₀ : ∀ v ∈ initial,G.degree v+2 ≤ G.maxDegree)
    (hThreshold : 2 ≤ threshold) (hTest : 1 ≤ test) (hCap : 0 < cap)
    (hSize : 4 ≤ initialᶜ.card)
    (hMargin : 5*initial.card+cap+4+(4*initial.card+2) ≤ floor)
    (hRange : floor+threshold+low.card ≤ G.maxDegree-2*m)
    (hRate : m*(2*(initial.card+1)) ≤ cap*cap) :
    H.AtBoundary limit ∨ Nonempty (OriginalTrimmingHistory G initial low threshold floor cap test (m+1)) := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  let d := G.maxDegree-2*m
  by_cases hStop : HasAlmostOverfullRecord (univ.filter (fun v => 0 < H.degree m v)) d test (H.degree m)
  · exact Or.inl (Or.inr (Or.inl hStop))
  have hU : H.exceptional m ⊆ initial := by
    have h := trimming_exceptional_sets_antitone H.exceptional
      (fun i => univ.filter (fun v => 0 < H.degree i v)) H.degree G.maxDegree threshold m
      H.exceptional_next m le_rfl 0 (Nat.zero_le _)
    rwa [H.exceptional_zero] at h
  have hLe : H.graph m ≤ G := by
    have h := virtual_trimming_prefix_le H.graph H.cleaned H.prescribed m
      (fun i hi => DeletionRun.le_source (H.cleanup i hi)) H.graph_next 0 m (Nat.zero_le _) le_rfl
    exact h.trans H.graph_zero.le
  have hIndependent : (H.graph m).IsIndepSet (↑(H.exceptional m ∩ low) : Set V) := by
    intro u hu v hv hne hEdge
    exact hInd (mem_inter.mp hu).2 (mem_inter.mp hv).2 hne (hLe hEdge)
  have hDef (v : V) (hv : v ∈ H.exceptional m) : H.degree m v+2 ≤ d := by
    cases m with
    | zero =>
      have hvI : v ∈ initial := by simpa only [H.exceptional_zero] using hv
      rw [H.degree_zero]
      simpa [d] using hDef₀ v hvI
    | succ m =>
      rw [H.exceptional_next m (Nat.lt_succ_self _)] at hv
      have h := (mem_filter.mp hv).2
      change threshold ≤ d-H.degree (m+1) v at h
      omega
  obtain ⟨hCore,hReserve⟩ := H.next_round_reserves hLow hInd hOrd hFloor hMargin hRange
  have hD : 2 ≤ d := by change floor+threshold+low.card ≤ d at hRange; omega
  obtain ⟨T,hRun,hSub,_,_,hLoss,hClean,hOutcome⟩ := exists_cleaned_trimming_selection (H.graph m)
    initial (H.exceptional m) (H.exceptional m ∩ low) hU inter_subset_left hIndependent
    H.prescribed H.credit d floor test hD hSize hTest H.free m cap cap (2*(initial.card+1))
    hCap H.free_size hRate
    (by rw [←H.degree_exact m le_rfl]; exact H.degree_bound m le_rfl)
    (by rw [←H.degree_exact m le_rfl]; exact hDef)
    (by rw [←H.degree_exact m le_rfl]; exact hCore) (fun v hv hw hp => (hReserve v hv hw hp).1)
  rcases hOutcome with hAlmost | hRound | hSwitch
  · exact Or.inl (Or.inr (Or.inr ⟨T,hRun,Or.inl hAlmost⟩))
  · let cleanDegree := auxiliaryPhysicalDegree T initial H.prescribed H.credit m
    let actualRecord (v : V) := H.degree m v-(sdiff (H.graph m) T).degree v
    have hEq : cleanDegree = actualRecord := by
      funext v
      rw [show cleanDegree v = _ from auxiliary_physical_degree_after_cleanup (H.graph m) T initial
        H.prescribed H.credit m hSub v,←H.degree_exact m le_rfl]
    have hRecord (v : V) : actualRecord v+(sdiff (H.graph m) T).degree v = H.degree m v := by
      rw [←hEq,H.degree_exact m le_rfl]
      exact hClean v
    have hSpace (v : V) (hv : v ∉ initial) : 2 ≤ actualRecord v := by
      have h := hCore v hv
      have hc := hLoss v
      dsimp only [actualRecord]
      omega
    have hSelected : Nonempty (TrimmingStepSelection T initial
        (H.exceptional m ∩ univ.filter (fun v => 0 < actualRecord v))
        (originalCleanActive low (H.exceptional m) T)
        actualRecord d floor H.free m cap) := by
      rw [←hEq]
      exact hRound
    obtain ⟨R⟩ := hSelected
    exact Or.inr (H.snoc T hRun hStop hSpace hRecord R)
  · exact Or.inl (Or.inr (Or.inr ⟨T,hRun,Or.inr hSwitch⟩))

set_option maxHeartbeats 2200000 in
/-- Iterate the paper's original-active mode to its first boundary.
Every preceding round has an actual prescription and cumulative budgets. -/
theorem exists_original_trimming_history_at_boundary
    (G : SimpleGraph V) [DecidableRel G.Adj] (initial low : Finset V)
    (threshold floor cap test limit : ℕ)
    (hLow : low ⊆ initial) (hInd : G.IsIndepSet (low : Set V))
    (hOrd : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+threshold)
    (hFloor : ∀ v ∈ initial,v ∉ low → floor ≤ G.degree v)
    (hDef₀ : ∀ v ∈ initial,G.degree v+2 ≤ G.maxDegree)
    (hThreshold : 2 ≤ threshold) (hTest : 1 ≤ test) (hCap : 0 < cap)
    (hSize : 4 ≤ initialᶜ.card)
    (hMargin : 5*initial.card+cap+4+(4*initial.card+2) ≤ floor)
    (hRange : floor+threshold+low.card ≤ G.maxDegree-2*limit)
    (hRate : limit*(2*(initial.card+1)) ≤ cap*cap) :
    ∃ m ≤ limit,∃ H : OriginalTrimmingHistory G initial low threshold floor cap test m,
      H.AtBoundary limit := by
  have loop (i : ℕ) (hi : i ≤ limit) :
      (∃ m ≤ i,∃ H : OriginalTrimmingHistory G initial low threshold floor cap test m,
        H.AtBoundary limit) ∨ Nonempty (OriginalTrimmingHistory G initial low threshold floor cap test i) := by
    induction i with
    | zero => exact Or.inr (original_trimming_history_zero G initial low threshold floor cap test)
    | succ i ih =>
      rcases ih (by omega) with ⟨m,hm,H,hEnd⟩ | hHistory
      · exact Or.inl ⟨m,by omega,H,hEnd⟩
      obtain ⟨H⟩ := hHistory
      have hLe : i ≤ limit := by omega
      have hRange' : floor+threshold+low.card ≤ G.maxDegree-2*i :=
        hRange.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hLe) _)
      have hRate' := (Nat.mul_le_mul_right (2*(initial.card+1)) hLe).trans hRate
      rcases H.continue_or_boundary limit hLow hInd hOrd hFloor hDef₀ hThreshold hTest hCap hSize
        hMargin hRange' hRate' with hEnd | hNew
      · exact Or.inl ⟨i,by omega,H,hEnd⟩
      · exact Or.inr hNew
  rcases loop limit le_rfl with hEnd | hHistory
  · exact hEnd
  · obtain ⟨H⟩ := hHistory
    exact ⟨limit,le_rfl,H,Or.inl rfl⟩

set_option maxHeartbeats 2300000 in
/-- Start and run the original-active part of Operation 4.1 from
the actual source graph with the paper's initial exceptional and low
sets. The size and density hypotheses pay for every prior selection. -/
theorem cms_operation_4_1_original_phase (G : SimpleGraph V) [DecidableRel G.Adj]
    (η : ℝ) (hη : 0 ≤ η) (hSmall : η ≤ 1/16)
    (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (test : ℕ) (hTest : 1 ≤ test) :
    let n := Fintype.card V
    let initial := initialExceptionalSet G η
    let low := initialLowSet G η
    let shift := η*(n:ℝ)
    let threshold := ⌈shift⌉₊
    let cap := ⌊shift⌋₊
    let limit := ⌊(G.maxDegree:ℝ)/3-shift⌋₊
    12 ≤ shift → 6 ≤ η^2*(n:ℝ) → 24*shift ≤ (G.maxDegree:ℝ) →
    (initial.card:ℝ) ≤ η^2*(n:ℝ) →
    ∃ m ≤ limit,∃ H : OriginalTrimmingHistory G initial low threshold limit cap test m,
      H.AtBoundary limit := by
  intro n initial low shift threshold cap limit hShift hSize hDense hFew
  have hLow : low ⊆ initial := filter_subset _ _
  have hCard : (low.card:ℝ) ≤ initial.card := by exact_mod_cast card_le_card hLow
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hηn : shift ≤ (n:ℝ)/16 := by
    have h := mul_le_mul_of_nonneg_right hSmall hn
    dsimp only [shift]
    linarith only [h]
  have hFew' : (initial.card:ℝ) ≤ shift/16 := by
    have h := mul_le_mul_of_nonneg_right hSmall (show 0 ≤ η*(n:ℝ) by positivity)
    dsimp only [shift]
    nlinarith only [h,hFew]
  have hV : 0 < n := by exact_mod_cast (show 0 < (n:ℝ) by linarith only [hShift,hηn])
  have : Nonempty V := Fintype.card_pos_iff.mp hV
  have hFloorNonneg : 0 ≤ (G.maxDegree:ℝ)/3-shift := by linarith only [hShift,hDense]
  have hL : (limit:ℝ) ≤ (G.maxDegree:ℝ)/3-shift := Nat.floor_le hFloorNonneg
  have hC : (threshold:ℝ) ≤ shift+1 := (Nat.ceil_lt_add_one (by linarith only [hShift])).le
  have hCN : shift ≤ (threshold:ℝ) := Nat.le_ceil _
  have hRange : limit+threshold+low.card+2*limit ≤ G.maxDegree := by
    exact_mod_cast (show (limit:ℝ)+threshold+low.card+2*limit ≤ G.maxDegree by
      linarith only [hL,hC,hCard,hFew',hShift])
  have hRounds : 3*limit ≤ n := by
    have hMax : (G.maxDegree:ℝ) ≤ n := by exact_mod_cast G.maxDegree_lt_card_verts.le
    exact_mod_cast (show (3:ℝ)*limit ≤ n by linarith only [hL,hMax,hShift])
  have hSum : (initial.card:ℝ)+(initialᶜ.card:ℝ) = n := by
    exact_mod_cast card_add_card_compl initial
  have hCore : 4 ≤ initialᶜ.card := by
    exact_mod_cast (show (4:ℝ) ≤ initialᶜ.card by linarith only [hSum,hηn,hShift,hFew'])
  have hCap : 0 < cap := by
    have h : 1 ≤ cap := Nat.le_floor (by simpa using (show (1:ℝ) ≤ shift by linarith only [hShift]))
    omega
  refine exists_original_trimming_history_at_boundary G initial low threshold limit cap test limit
    hLow (initial_low_set_independent G η hη hVAL) ?_ ?_ ?_
    (by exact_mod_cast (show (2:ℝ) ≤ threshold by linarith only [hShift,hCN])) hTest hCap hCore
    (cms_projection_margin_after_trimming_losses n G.maxDegree initial.card η hη hSmall
      hShift (by simpa only [shift,mul_assoc] using hDense) hFew) (by omega)
    (free_projection_budget_at_trimming_limit n limit initial.card η hRounds hShift hSize hFew)
  · intro v hv
    have h : (G.maxDegree:ℝ)-G.degree v ≤ shift := by
      by_contra! h'
      exact hv (mem_filter.mpr ⟨mem_univ _,h'⟩)
    exact_mod_cast (show (G.maxDegree:ℝ) ≤ (G.degree v:ℝ)+threshold by linarith only [h,hCN])
  · intro v hv hw
    have h : (G.maxDegree:ℝ)/3-shift ≤ G.degree v := by
      by_contra! h'
      exact hw (mem_filter.mpr ⟨hv,h'⟩)
    exact_mod_cast hL.trans h
  · intro v hv
    have h := (mem_filter.mp hv).2
    change shift < (G.maxDegree:ℝ)-G.degree v at h
    exact_mod_cast (show (G.degree v:ℝ)+2 ≤ G.maxDegree by linarith only [h,hShift])

set_option maxHeartbeats 2600000 in
/-- A history reaching the long limit without a switch has at most one
original active vertex left. If two survived, every cleaned round
would have prescribed a loss at both. -/
theorem OriginalTrimmingHistory.low_survivors_at_long_limit
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial low : Finset V}
    {threshold floor cap test : ℕ} (limit : ℝ)
    (H : OriginalTrimmingHistory G initial low threshold floor cap test ⌊limit⌋₊)
    (hLow : low ⊆ initial) (hPositive : 0 < ⌊limit⌋₊)
    (hStart : ∀ v ∈ low,(G.degree v:ℝ) < limit) :
    (H.exceptional ⌊limit⌋₊ ∩ low).card ≤ 1 := by
  let m := ⌊limit⌋₊
  let W (i : ℕ) := H.exceptional i ∩ low
  change (W m).card ≤ 1
  by_contra! hMany
  have hNested := trimming_exceptional_sets_antitone H.exceptional
    (fun i => univ.filter (fun v => 0 < H.degree i v)) H.degree G.maxDegree threshold m
    H.exceptional_next
  have hLive (i : ℕ) (hi : 0 < i) (hi' : i ≤ m) (v : V) (hv : v ∈ H.exceptional i) :
      0 < H.degree i v := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [H.exceptional_next j (by omega)] at hv
    exact (mem_filter.mp (mem_inter.mp (mem_filter.mp hv).1).2).2
  have hTerm : (W m).card ≤ 1 := by
    apply low_set_card_le_one_at_floored_long_limit W H.degree limit
    · intro i hi
      intro v hv
      obtain ⟨hU,hLow⟩ := mem_inter.mp hv
      exact mem_inter.mpr ⟨hNested (i+1) (by omega) i (by omega) hU,hLow⟩
    · intro v hv
      rw [H.degree_zero]
      exact hStart v (mem_inter.mp hv).2
    · intro i hi _ v hv
      obtain ⟨_,R,hP,hCredit,_,_,_⟩ := H.selection i hi
      have hS (j : ℕ) (hj : i+1 ≤ j) (hj' : j ≤ m) : H.graph j ≤ H.cleaned i := by
        have hSub : H.graph (i+1) ≤ H.cleaned i := by
          rw [H.graph_next i hi]
          exact fun _ _ h => h.1
        exact (virtual_trimming_prefix_le H.graph H.cleaned H.prescribed m
          (fun k hk => DeletionRun.le_source (H.cleanup k hk)) H.graph_next (i+1) j hj hj').trans hSub
      have hSurvive (j : ℕ) (hj : i+1 ≤ j) (hj' : j ≤ m) :
          W j ⊆ originalCleanActive low (H.exceptional i) (H.cleaned i) := by
        intro w hw
        obtain ⟨hwU,hwLow⟩ := mem_inter.mp hw
        have hPos := hLive j (by omega) hj' w hwU
        rw [H.degree_exact j hj',auxiliaryPhysicalDegree,if_pos (hLow hwLow)] at hPos
        exact mem_filter.mpr ⟨mem_inter.mpr ⟨hNested j hj' i (by omega) hwU,hwLow⟩,
          hPos.trans_le (degree_le_of_le (hS j hj hj'))⟩
      have hTwo : 2 ≤ (originalCleanActive low (H.exceptional i) (H.cleaned i)).card :=
        (show 2 ≤ (W m).card by omega).trans (card_le_card (hSurvive m (by omega) le_rfl))
      have hDrop := R.active_progress (Or.inl hTwo) v
        (hSurvive (i+1) le_rfl (by omega) hv)
      have hSum := R.round.words.prescribed_degree_add_credit_on_exceptional
        R.round.omitted (hLow (mem_inter.mp hv).2)
      have hD := H.degree_next i hi v
      rw [hCredit] at hD
      omega
    · intro v hv
      exact hLive m hPositive le_rfl v (mem_inter.mp hv).1
  omega

end OverfullWork.CMSTrimmingRound
