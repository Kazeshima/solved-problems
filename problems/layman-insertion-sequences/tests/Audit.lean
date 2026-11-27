import Insertion.Core
import Insertion.Families
import Insertion.OEIS

open Insertion

#print Insertion.pass
#print Insertion.stage
#print Insertion.IsLimit
#print Insertion.runLen
#print Insertion.next
#print Insertion.state
#print Insertion.rdis

#check @isLimit_rdis
#check @IsLimit.unique
#check @next_eq
#check @layman_C2
#check @layman_C2_twin
#check @layman_C4
#check @layman_C4_between
#check @A082630_rec
#check @A082630_prod
#check @A082630_square_even
#check @A082630_square_odd
#check @A082981_rec
#check @A085260_rec
#check @A085260_prod
#check @A085376_rec
#check @A085376_prod
#check @A085348_rec
#check @A085348_prod
#check @A085349_rec
#check @A085349_prod

#print axioms isLimit_rdis
#print axioms IsLimit.unique
#print axioms next_eq
#print axioms layman_C2
#print axioms layman_C2_twin
#print axioms layman_C4
#print axioms layman_C4_between
#print axioms A082630_values
#print axioms A082630_rec
#print axioms A082630_prod
#print axioms A082630_square_even
#print axioms A082630_square_odd
#print axioms A082981_values
#print axioms A082981_rec
#print axioms A085260_values
#print axioms A085260_rec
#print axioms A085260_prod
#print axioms A085376_values
#print axioms A085376_rec
#print axioms A085376_prod
#print axioms A085348_values
#print axioms A085348_rec
#print axioms A085348_prod
#print axioms A085349_values
#print axioms A085349_rec
#print axioms A085349_prod

-- the definitions reproduce the data in the OEIS entries
example : (List.range 13).map (rdis 7 11) = [1, 2, 5, 8, 19, 30, 71, 112, 265, 418, 989, 1560, 3691] := by decide
example : (List.range 13).map (rdis 4 5) = [1, 2, 3, 4, 9, 14, 19, 24, 53, 82, 111, 140, 309] := by decide
example : (List.range 8).map (rdis 833344 10000000) = [1, 12, 155, 2003, 25884, 334489, 4322473, 55857660] := by decide
example : (List.range 10).map (rdis 36704 100000) = [1, 3, 11, 30, 109, 297, 1079, 2940, 10681, 29103] := by decide
example : (List.range 9).map (rdis 264 1000) = [1, 4, 19, 72, 341, 1292, 6119, 23184, 109801] := by decide
example : (List.range 9).map (rdis 26688 100000) = [1, 4, 15, 71, 269, 1274, 4827, 22861, 86617] := by decide
-- the literal insertion passes: after 9 passes the first seven terms of A082630 are in place
example : (stage 7 11 9).take 7 = [1, 2, 5, 8, 19, 30, 71] := by decide
