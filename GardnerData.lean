import GardnerDefs
namespace Gardner

def witness : List Square := [(0,2), (0,8), (2,0), (2,22), (4,16), (4,24), (6,6), (6,10), (8,0), (8,24), (10,6), (10,26), (11,1), (12,14), (12,18), (14,12), (14,20), (16,4), (16,28), (18,12), (18,22), (20,14), (20,28), (22,2), (22,18), (24,4), (24,8), (26,10), (26,26), (28,16), (28,20)]

def witnessLines : List (Dir × Nat) := [(.row,0), (.row,2), (.row,4), (.row,6), (.row,8), (.row,10), (.row,12), (.row,14), (.row,16), (.row,18), (.row,20), (.row,22), (.row,24), (.row,26), (.row,28), (.col,0), (.col,2), (.col,4), (.col,6), (.col,8), (.col,10), (.col,12), (.col,14), (.col,16), (.col,18), (.col,20), (.col,22), (.col,24), (.col,26), (.col,28), (.sum,2), (.sum,8), (.sum,12), (.sum,16), (.sum,20), (.sum,24), (.sum,26), (.sum,28), (.sum,30), (.sum,32), (.sum,34), (.sum,36), (.sum,40), (.sum,44), (.sum,48), (.diff,9), (.diff,13), (.diff,17), (.diff,21), (.diff,23), (.diff,25), (.diff,27), (.diff,29), (.diff,31), (.diff,33), (.diff,35), (.diff,37), (.diff,41), (.diff,45), (.diff,49)]

end Gardner
