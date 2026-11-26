import Quadric.Five.Resources.FirstCount
import Quadric.Five.Resources.Count00
import Quadric.Five.Resources.Count01
import Quadric.Five.Resources.Count02
import Quadric.Five.Resources.Count03
import Quadric.Five.Resources.Count04
import Quadric.Five.Resources.Count05
import Quadric.Five.Resources.Count06
import Quadric.Five.Resources.Count07
import Quadric.Five.Resources.Count08
import Quadric.Five.Resources.Count09
import Quadric.Five.Resources.Count10
import Quadric.Five.Resources.Count11
import Quadric.Five.Resources.Count12
import Quadric.Five.Resources.Count13
import Quadric.Five.Resources.Count14
import Quadric.Five.Resources.Count15
import Quadric.Five.Resources.Count16
import Quadric.Five.Resources.Count17
namespace Quadric.Five.Census
theorem completion_census_count : ((Block.Case00.rows.map rowCount).sum + (Block.Case01.rows.map rowCount).sum + (Block.Case02.rows.map rowCount).sum + (Block.Case03.rows.map rowCount).sum + (Block.Case04.rows.map rowCount).sum + (Block.Case05.rows.map rowCount).sum + (Block.Case06.rows.map rowCount).sum + (Block.Case07.rows.map rowCount).sum + (Block.Case08.rows.map rowCount).sum + (Block.Case09.rows.map rowCount).sum + (Block.Case10.rows.map rowCount).sum + (Block.Case11.rows.map rowCount).sum + (Block.Case12.rows.map rowCount).sum + (Block.Case13.rows.map rowCount).sum + (Block.Case14.rows.map rowCount).sum + (Block.Case15.rows.map rowCount).sum + (Block.Case16.rows.map rowCount).sum + (Block.Case17.rows.map rowCount).sum)=34224 := by
  rw [Block.Case00.total_hits,Block.Case01.total_hits,Block.Case02.total_hits,Block.Case03.total_hits,Block.Case04.total_hits,Block.Case05.total_hits,Block.Case06.total_hits,Block.Case07.total_hits,Block.Case08.total_hits,Block.Case09.total_hits,Block.Case10.total_hits,Block.Case11.total_hits,Block.Case12.total_hits,Block.Case13.total_hits,Block.Case14.total_hits,Block.Case15.total_hits,Block.Case16.total_hits,Block.Case17.total_hits]
noncomputable def censusRows : List (List Block.Row) := [Block.Case00.rows,Block.Case01.rows,Block.Case02.rows,Block.Case03.rows,Block.Case04.rows,Block.Case05.rows,Block.Case06.rows,Block.Case07.rows,Block.Case08.rows,Block.Case09.rows,Block.Case10.rows,Block.Case11.rows,Block.Case12.rows,Block.Case13.rows,Block.Case14.rows,Block.Case15.rows,Block.Case16.rows,Block.Case17.rows]
theorem unique_completions : censusRows.all (fun rs=>rs.all blockUnique)=true := by
  simp only [censusRows,List.all_cons,List.all_nil,Block.Case00.bounded_unique,Block.Case01.bounded_unique,Block.Case02.bounded_unique,Block.Case03.bounded_unique,Block.Case04.bounded_unique,Block.Case05.bounded_unique,Block.Case06.bounded_unique,Block.Case07.bounded_unique,Block.Case08.bounded_unique,Block.Case09.bounded_unique,Block.Case10.bounded_unique,Block.Case11.bounded_unique,Block.Case12.bounded_unique,Block.Case13.bounded_unique,Block.Case14.bounded_unique,Block.Case15.bounded_unique,Block.Case16.bounded_unique,Block.Case17.bounded_unique,Bool.and_self]
private theorem distinctSum (rs : List Block.Row) (hr : rs.all blockUnique=true) :
    (rs.map distinctRowCount).sum=(rs.map rowCount).sum := by
  congr 1; apply List.map_congr_left; intro r h; exact (row_distinct (List.all_eq_true.mp hr r h)).2
theorem distinct_completion_count : (censusRows.map (fun rs=>(rs.map distinctRowCount).sum)).sum=34224 := by
  have eq : censusRows.map (fun rs=>(rs.map distinctRowCount).sum)=censusRows.map (fun rs=>(rs.map rowCount).sum) := by
    apply List.map_congr_left; intro rs hr; exact distinctSum rs (List.all_eq_true.mp unique_completions rs hr)
  rw [eq]; simp only [censusRows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Block.Case00.total_hits,Block.Case01.total_hits,Block.Case02.total_hits,Block.Case03.total_hits,Block.Case04.total_hits,Block.Case05.total_hits,Block.Case06.total_hits,Block.Case07.total_hits,Block.Case08.total_hits,Block.Case09.total_hits,Block.Case10.total_hits,Block.Case11.total_hits,Block.Case12.total_hits,Block.Case13.total_hits,Block.Case14.total_hits,Block.Case15.total_hits,Block.Case16.total_hits,Block.Case17.total_hits,Nat.reduceAdd]
end Quadric.Five.Census
