module

public import OverfullWork.BipartiteRobustMargin
public import OverfullWork.RegularCompletionPartition

@[expose] public section


/-! # Bipartite expansion on the actual controlled completion cut

An actual regular multigraph contains the supplied simple graph. At
vertices of small degree deficit, the SAME cut's weighted discrepancy
forces large simple crossing degrees. The finite counting criterion
then proves bipartite robust expansion, without assuming that conclusion.
-/
namespace OverfullWork.CompletionBipartiteRobust
open SimpleGraph Finset PrunedCore BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem simple_degreeInto_eq_neighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) : (MultiGraph.ofSimpleGraph G).degreeInto A v=neighboursIn G A v := by
  rw [RobustExpansion.neighboursIn_eq_filter_card,card_filter]
  simp only [MultiGraph.degreeInto,MultiGraph.ofSimpleGraph,SimpleGraph.mem_edgeSet]

theorem degreeInto_mono (M N : MultiGraph V) (hsub : ∀e,M.mult e≤N.mult e)
    (A : Finset V) (v : V) : M.degreeInto A v≤N.degreeInto A v :=
  sum_le_sum (fun _ _=>hsub _)

theorem degreeInto_simple_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : MultiGraph V) (D : ℕ) (hreg : M.IsRegularOfDegree D)
    (hsub : ∀e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e) (A : Finset V) (v : V) :
    M.degreeInto A v≤neighboursIn G A v+(D-G.degree v) := by
  have h₁:=degreeInto_mono _ M hsub Aᶜ v
  have h₂:=(MultiGraph.ofSimpleGraph G).degreeInto_add_compl A v
  have h₃:=M.degreeInto_add_compl A v
  have h₄:=MultiGraph.degree_subtract_add M (MultiGraph.ofSimpleGraph G) hsub v
  rw [MultiGraph.degree_ofSimpleGraph,hreg v] at h₄
  rw [simple_degreeInto_eq_neighbours] at h₁
  rw [simple_degreeInto_eq_neighbours,simple_degreeInto_eq_neighbours,
    MultiGraph.degree_ofSimpleGraph] at h₂
  rw [hreg v] at h₃
  omega

theorem crossing_degree_of_small_deficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : MultiGraph V) (D : ℕ) (hreg : M.IsRegularOfDegree D)
    (hsub : ∀e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e)
    (A : Finset V) (v : V) (b : ℝ) (s δ : ℕ)
    (hDis : |(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)|<b+((D-G.degree v:ℕ):ℝ))
    (hDef : D-G.degree v≤s) (hRoom : 2*(δ:ℝ)+b+3*(s:ℝ)≤D) :
    δ≤neighboursIn G A v ∧ δ≤neighboursIn G Aᶜ v := by
  have hA:=degreeInto_simple_loss G M D hreg hsub A v
  have hB:=degreeInto_simple_loss G M D hreg hsub Aᶜ v
  have hSum:=M.degreeInto_add_compl A v
  rw [hreg v] at hSum
  have hA':(M.degreeInto A v:ℝ)≤(neighboursIn G A v:ℝ)+((D-G.degree v:ℕ):ℝ):=by exact_mod_cast hA
  have hB':(M.degreeInto Aᶜ v:ℝ)≤(neighboursIn G Aᶜ v:ℝ)+((D-G.degree v:ℕ):ℝ):=by exact_mod_cast hB
  have hSum':(M.degreeInto A v:ℝ)+(M.degreeInto Aᶜ v:ℝ)=(D:ℝ):=by exact_mod_cast hSum
  have hDef':((D-G.degree v:ℕ):ℝ)≤(s:ℝ):=by exact_mod_cast hDef
  obtain ⟨hLeft,hRight⟩:=abs_lt.mp hDis
  have hGoodA:(δ:ℝ)≤(neighboursIn G A v:ℝ):=by linarith
  have hGoodB:(δ:ℝ)≤(neighboursIn G Aᶜ v:ℝ):=by linarith
  exact ⟨by exact_mod_cast hGoodA,by exact_mod_cast hGoodB⟩

/-- A proved criterion on the already constructed cut. Deficits outside
the actual finite exceptional set and all scale costs remain explicit. -/
theorem robust_of_completed_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : MultiGraph V) (D : ℕ) (hreg : M.IsRegularOfDegree D)
    (hsub : ∀e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e)
    (A E : Finset V) (m δ q r t a s : ℕ) (b : ℝ)
    (hA : A.card=m) (hB : Aᶜ.card=m) (hE : E.card≤a)
    (hDis : ∀v,|(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)|<b+((D-G.degree v:ℕ):ℝ))
    (hDef : ∀v,v∉E → D-G.degree v≤s)
    (hRoom : 2*(δ:ℝ)+b+3*(s:ℝ)≤D)
    (hδ : δ≤m) (hMargin : m+2*q≤2*δ) (hr : 0<r)
    (hrq : r≤q) (hrt : r+a≤t) (hScale : 4*r*m+2*m*a≤q*t) :
    IsBipartiteRobustAt G A r t := by
  apply bipartite_robust_of_margin G A E m δ q r t a hA hB hE
  · intro v _ hv
    exact (crossing_degree_of_small_deficit G M D hreg hsub A v b s δ
      (hDis v) (hDef v hv) hRoom).2
  · intro v _ hv
    exact (crossing_degree_of_small_deficit G M D hreg hsub A v b s δ
      (hDis v) (hDef v hv) hRoom).1
  all_goals assumption

end OverfullWork.CompletionBipartiteRobust
