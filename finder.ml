(* Objective Caml program to solve the "five queens and five knights"
   problem.  Laura Dean, October 14, 2003. *)

(* This file is structured as follows:
   * introduction
   * basic chessboard functions
   * functions to count ways of placing pieces
   * test functions -- not technically part of the solution,
     but they do increase my confidence in it
   * the "main" method (which is called _, not main, in ocaml).
 *)

(* The algorithm is a pretty simple depth-first search, improved by
   the following insights.

   Note that rows are numbered 0-7, top to bottom, and
   columns are numbered 0-7, left to right.

   1. If a queen is put into column x, then no other queens may be put
      into that column, so the search for the next queen's position
      should begin in column x+1.

      Also, if at any point we are trying to put m queens into x
      columns, and m>x, then there are no solutions to be found on
      this branch of the search.

   2. If knight A is attacking knight B, then B also attacks A;
      if queen C is attacking queen D, then D also attacks C.

      Thus if we have placed only queens on the board, and want to
      know whether it's safe to place a queen in a certain square, we
      need know only whether that square is attacked; there's no need
      to ask whether the new piece would attack other pieces.  This is
      not the case when knights come into play, of course.

   3. The leftmost queen will be in rows 0-3 (the upper half of the
      board) in half the solutions: the other half may be obtained by
      taking the mirror images (across a horizontal axis) of those in
      the first half.

   4. I called it "five queens and five knights" because 6 is too high.
      This can be seen by considering the actions of queens on their
      rows and columns.  (Diagonals are harder to reason about.)

      With 8 queens on the board, all squares are attacked, and so
      no knight may be placed.  With 7 queens on the board, all but 1
      row and all but 1 column contain a queen; that row and that
      column intersect in one square, which is not room for 7 knights.

      With 6 queens on the board, there is a queen in all but 2 rows
      and all but 2 columns.  Those 2 rows and 2 columns intersect in
      4 squares: as before, not enough room for 6 knights.

      So we reach 5.  The 3 free rows and 3 free columns intersect in
      9 squares, so there may be room for 5 knights.  This is where the
      computer comes in.

 *)


(* ========== functions for manipulating chessboards ========== *)

(* A chessboard is represented by an 8x8 array.  That means they're
   mutable.  In order to try a possible piece-placement in a search,
   then, it's important to copy the board first. *)
(* Note that throughout the code, there are places where x
   and y inputs are assumed to be between 0 and 7 inclusive.
   This assumption is ok in this context, but if we were allowing user
   input or creating a public API, things might be different. *)

type square = Open | Attacked | Queen | Knight;;

(* Creates an empty chessboard, in which every square is a valid place
   to put a piece -- that is, it is neither occupied nor attacked. *)
let create_empty_board () =
  Array.create_matrix 8 8 Open;
;;

(* Creates a copy of a board. *)
let copy_board board =
  let copy_column i column = Array.copy column in
  Array.mapi copy_column board
;;

(* Helpers for place_queen.
   These functions could be turned into one function with more parameters,
   but the resulting code would be less readable and no faster. *)
let rec invalidate_diag_upleft board x y =
  if (x >= 0 && y >= 0) then
    (board.(x).(y) <- Attacked;
     invalidate_diag_upleft board (x-1) (y-1))
;;
let rec invalidate_diag_downleft board x y =
  if (x >= 0 && y <= 7) then
    (board.(x).(y) <- Attacked;
     invalidate_diag_downleft board (x-1) (y+1))
;;
let rec invalidate_diag_upright board x y =
  if (x <= 7 && y >= 0) then
    (board.(x).(y) <- Attacked;
     invalidate_diag_upright board (x+1) (y-1))
;;
let rec invalidate_diag_downright board x y =
  if (x <= 7 && y <= 7) then
    (board.(x).(y) <- Attacked;
     invalidate_diag_downright board (x+1) (y+1))
;;

(* Marks as invalid the queen's square and those she attacks. *)
let place_queen board x y =
  for i=0 to 7 do
    board.(i).(y) <- Attacked
  done;
  for j=0 to 7 do
    board.(x).(j) <- Attacked
  done;
  invalidate_diag_downleft board (x-1) (y+1);
  invalidate_diag_upleft board (x-1) (y-1);
  invalidate_diag_downright board (x+1) (y+1);
  invalidate_diag_upright board (x+1) (y-1);
  board.(x).(y) <- Queen;
;;

(* Marks as invalid the knight's square and those he attacks. *)
let place_knight board x y =
  if x>0 then
    (if y>1 then
      board.(x-1).(y-2) <- Attacked;
     if y<6 then
       board.(x-1).(y+2) <- Attacked;
     if x>1 then
       (if y>0 then
         board.(x-2).(y-1) <- Attacked;
        if y<7 then
          board.(x-2).(y+1) <- Attacked));
  if x<7 then
    (if y>1 then
      board.(x+1).(y-2) <- Attacked;
     if y<6 then
       board.(x+1).(y+2) <- Attacked;
     if x<6 then
       (if y>0 then
         board.(x+2).(y-1) <- Attacked;
        if y<7 then
          board.(x+2).(y+1) <- Attacked));
  board.(x).(y) <- Knight;
;;

(* Returns true if a knight may be placed in square (x,y)
   without attacking a queen.  This function ignores the question
   of whether (x,y) itself is already occupied or attacked.

   I tried several versions of this function, including a large
   hard-to-read boolean expression and a version that checked
   against a list of queens rather than checking for queens in
   all 8 (at most) squares.  Strangely enough, this one won. *)
let can_place_knight board x y =
  let ok = ref true in
  if x>0 then
    (if
      (y>1 && board.(x-1).(y-2) = Queen) ||
      (y<6 && board.(x-1).(y+2) = Queen) then
      ok := false
    else if x>1 then
      (if
        (y>0 && board.(x-2).(y-1) = Queen) ||
        (y<7 && board.(x-2).(y+1) = Queen) then
        ok := false));
  (* note that in ocaml, "!" means "dereference", not "not" *)
  if x<7 && !ok then
    (if
      (y>1 && board.(x+1).(y-2) = Queen) ||
      (y<6 && board.(x+1).(y+2) = Queen) then
      ok := false
    else if x<6 then
      (if
        (y>0 && board.(x+2).(y-1) = Queen) ||
        (y<7 && board.(x+2).(y+1) = Queen) then
        ok := false));
  !ok;
;;


(* ==== functions for finding valid knight and queen placements ==== *)

(* Places n knights on the board, starting from square (x,y).
   Returns the number of different ways to make such a placement. *)
let rec place_n_knights board n x y =
  if n=0 then
    1
  else if x>7 then
    0
  else if y>7 then
    place_n_knights board n (x+1) 0
  else
    match board.(x).(y) with
      Open ->
        (if can_place_knight board x y then
          let new_board = copy_board board in
          place_knight new_board x y;
          (place_n_knights new_board (n-1) x (y+1))
            + (place_n_knights board n x (y+1))
        else
          place_n_knights board n x (y+1))
    | _ ->
        place_n_knights board n x (y+1)
;;

(* Places m queens and n knights on the board, starting from square (x,y).
   Returns the number of different ways to make such a placement. *)
let rec place_m_queens_n_knights board m n x y =
  if m=0 then
    place_n_knights board n 0 0
  else if m>(8-x) || x>7 then
    0
  else if y>7 then
    place_m_queens_n_knights board m n (x+1) 0
  else
    match board.(x).(y) with
      Open ->
        (let new_board = copy_board board in
        place_queen new_board x y;
        (place_m_queens_n_knights new_board (m-1) n (x+1) 0)
          + (place_m_queens_n_knights board m n x (y+1)))
    | _ ->
        place_m_queens_n_knights board m n x (y+1)
;;

(* An optimized version of place_m_queens_k_knights: searches only the
   first 4 rows in the first column containing a queen.  This function
   makes sense only on an empty board (in the context of this
   problem), and so it creates its own.  As the name suggests, it
   finds half as many possibilities as the regular version. *)
let rec half_m_queens_n_knights m n x y =
  let board = create_empty_board() in
  if x>3 then
    0
  else if y>3 then
    half_m_queens_n_knights m n (x+1) 0
  else
    match board.(x).(y) with
      Open ->
        (let new_board = copy_board board in
        place_queen new_board x y;
        (place_m_queens_n_knights new_board (m-1) n (x+1) 0)
          + (half_m_queens_n_knights m n x (y+1)))
    | _ ->
        half_m_queens_n_knights m n x (y+1)
;;


(* ================ testing functions ================ *)

(* In the interest of saving space and reducing clutter,
   these sample test cases are not meant to be exhaustive. *)

let test_placing_one_knight () =
  let board = create_empty_board() in
  let n_found = (place_n_knights board 1 0 0) in
  if n_found != 64 then
    print_string ("Error in test_placing_one_knight: should be 64, but got "
                  ^ string_of_int n_found ^ "\n");

  (* 9 squares are invalidated, so we expect (64-9) valid ones *)
  let board = create_empty_board () in
  place_knight board 4 4;
  let n_found = (place_n_knights board 1 0 0) in
  if n_found != 55 then
    print_string ("Error in test_placing_one_knight: should be 55, but got "
                  ^ string_of_int n_found ^ "\n");

  (* 28 squares are attacked by the queen, and
     there are 8 squares from which a knight would attack the queen,
     so we expect (64-28-8) valid ones *)
  let board = create_empty_board () in
  place_queen board 4 4;
  let n_found = (place_n_knights board 1 0 0) in
  if n_found != 28 then
    print_string ("Error in test_placing_one_knight: should be 28, but got "
                  ^ string_of_int n_found ^ "\n");
;;

(* the eight queens problem *)
let test_eight_queens () =
  let board = create_empty_board() in
  let n_found = place_m_queens_n_knights board 8 0 0 0 in
  if n_found != 92 then
    print_string ("Error in test_eight_queens: "
                  ^ string_of_int n_found ^ "\n");
  let half_found = half_m_queens_n_knights 8 0 0 0 in
  if half_found != 46 then
    print_string ("Error in test_eight_queens (half): "
                  ^ string_of_int n_found ^ "\n");
;;

(* test that the optimized half_m_queens_n_knights does the right thing
   (namely, finding exactly half of the possibilities) *)
let test_half_finder () =
  let board = create_empty_board() in
  let n_found = place_m_queens_n_knights board 5 0 0 0 in
  let n_found_half = half_m_queens_n_knights 5 0 0 0 in
  if (n_found_half * 2) != n_found then
    print_string ("Error in test_half_finder: "
                  ^ string_of_int n_found ^ "found by full finder, but "
                  ^ string_of_int n_found_half
                  ^ " found by half finder.\n");

  let n_found = place_m_queens_n_knights board 5 6 0 0 in
  let n_found_half = half_m_queens_n_knights 5 6 0 0 in
  if (n_found_half * 2) != n_found then
    print_string ("Error in test_half_finder: "
                  ^ string_of_int n_found ^ "found by full finder, but "
                  ^ string_of_int n_found_half
                  ^ " found by half finder.\n");
;;

(* we know there's no way to place six queens and six knights *)
let test_six_queens_knights () =
  let board = create_empty_board() in
  let n_found = place_m_queens_n_knights board 6 6 0 0 in
  if n_found != 0 then
    print_string ("Error in test_six_queens_knights: "
                  ^ string_of_int n_found ^ "\n");
;;

(* test at least a few of the knight attack places *)
let test_can_place_knight () =
  let board = create_empty_board() in
  board.(4).(4) <- Queen;
  if can_place_knight board 5 6 then
    print_string ("Error in test_can_place_knight: 4,4; 5,6\n");
  if can_place_knight board 6 5 then
    print_string ("Error in test_can_place_knight: 4,4; 6,5\n");
  if can_place_knight board 3 6 then
    print_string ("Error in test_can_place_knight: 4,4; 3,6\n");
  if can_place_knight board 6 3 then
    print_string ("Error in test_can_place_knight: 4,4; 6,3\n");

  if not (can_place_knight board 5 5) then
    print_string ("Error in test_can_place_knight: 4,4; 5,5\n");

  let board = create_empty_board() in
  board.(0).(4) <- Queen;
  if can_place_knight board 1 6 then
    print_string ("Error in test_can_place_knight: 0,4; 1,6\n");
  if can_place_knight board 2 5 then
    print_string ("Error in test_can_place_knight: 0,4; 2,5\n");
  if can_place_knight board 2 3 then
    print_string ("Error in test_can_place_knight: 0,4; 2,3\n");
  if can_place_knight board 1 2 then
    print_string ("Error in test_can_place_knight: 0,4; 1,2\n");

  (* many others were included here, but they're not interesting *)
;;


(* ========= main (not actually called "main") ========= *)

let _ =
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "test" then
    (test_placing_one_knight ();
     test_can_place_knight ();
     test_eight_queens ();
     test_half_finder ();
     test_six_queens_knights ())
  else
    let half = half_m_queens_n_knights 5 5 0 0 in
    print_string (string_of_int (half * 2) ^ "\n");
;;
