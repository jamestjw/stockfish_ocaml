let matrix_get matrix i j = Array.get (Array.get matrix i) j
let matrix_set matrix i j value = Array.set (Array.get matrix i) j value

(*
 * # 1--2;;
 * - : int list = [1; 2]
 * # 1--5;;
 * - : int list = [1; 2; 3; 4; 5]
 * # 5--10;;
 * - : int list = [5; 6; 7; 8; 9; 10]
 *)
let ( -- ) i j =
  let rec aux n acc = if n < i then acc else aux (n - 1) (n :: acc) in
  aux j []
