open Core_kernel

module CellState = struct
  type 'a t =
    | Unknown
    | Known of 'a
    | Contradiction

  include Monad.Make (struct
    type nonrec 'a t = 'a t

    let bind x ~f =
      match x with
      | Unknown -> Unknown
      | Known x -> f x
      | Contradiction -> Contradiction
    ;;

    let return x = Known x

    let map =
      `Custom
        (fun x ~f ->
          match x with
          | Unknown -> Unknown
          | Known x -> Known (f x)
          | Contradiction -> Contradiction)
    ;;
  end)

  let lift ~f a b =
    let open Let_syntax in
    let%map a = a
    and b = b in
    f a b
  ;;
end

module Cell = struct
  type opaque_t = Opaque : 'a t -> opaque_t

  and 'a t =
    { mutable state : 'a CellState.t
    ; mutable triggers : (opaque_t * ('a CellState.t -> unit)) list
    ; equal : 'a -> 'a -> bool
    }

  let create ~equal = { state = Unknown; triggers = []; equal }

  let update_internal (t : 'a t) (new_state : 'a CellState.t) ?caller () =
    match t.state, new_state with
    | Unknown, Unknown | Contradiction, _ | _, Contradiction -> ()
    | Known x, Known y when t.equal x y -> ()
    | Known _, Known _ ->
      t.state <- Contradiction;
      List.iter t.triggers ~f:(fun (_, f) -> f Contradiction)
    | Unknown, Known x | Known x, Unknown ->
      t.state <- Known x;
      (match caller with
      | None -> List.iter t.triggers ~f:(fun (_, f) -> f (Known x))
      | Some caller ->
        List.iter t.triggers ~f:(fun (Opaque t', f) ->
            if not (phys_same caller t') then f (Known x)))
  ;;

  let update t a = update_internal t (Known a) ~caller:None ()

  let query t =
    match t.state with
    | Unknown -> None
    | Contradiction -> None
    | Known x -> Some x
  ;;

  let add_trigger t ~from ~f =
    t.triggers <- (Opaque from, f) :: t.triggers;
    f t.state
  ;;

  let binary (a : 'a t) (b : 'b t) ~(f : 'a -> 'b) ~(g : 'b -> 'a) =
    add_trigger a ~from:b ~f:(fun new_state ->
        update_internal b (CellState.map ~f new_state) ~caller:a ());
    add_trigger b ~from:a ~f:(fun new_state ->
        update_internal a (CellState.map ~f:g new_state) ~caller:b ())
  ;;

  let ternary
      (a : 'a t)
      (b : 'b t)
      (c : 'b t)
      ~(f : 'a -> 'b -> 'c)
      ~(g : 'b -> 'c -> 'a)
      ~(h : 'c -> 'a -> 'b)
    =
    add_trigger a ~from:b ~f:(fun new_state ->
        update_internal b (CellState.lift ~f:h c.state new_state) ~caller:a ());
    add_trigger a ~from:c ~f:(fun new_state ->
        update_internal c (CellState.lift ~f new_state b.state) ~caller:a ());
    add_trigger b ~from:a ~f:(fun new_state ->
        update_internal a (CellState.lift ~f:g new_state c.state) ~caller:b ());
    add_trigger b ~from:c ~f:(fun new_state ->
        update_internal c (CellState.lift ~f a.state new_state) ~caller:b ());
    add_trigger c ~from:a ~f:(fun new_state ->
        update_internal a (CellState.lift ~f:g b.state new_state) ~caller:c ());
    add_trigger c ~from:b ~f:(fun new_state ->
        update_internal b (CellState.lift ~f:h new_state a.state) ~caller:c ())
  ;;

  (*
  let many (as_ : 'a t list) (b: 'b t) ~(f : 'a list -> 'b) ~(g : 'a list -> 'b -> 'a) =
    List.iter as_ ~f:(fun a ->
      add_trigger a ~from:b ~f:(fun new_state ->
        update_internal b 
    );
    *)
end

let fneg a b = Float.(Cell.binary a b ~f:neg ~g:neg)
let fadd a b c = Float.(Cell.ternary a b c ~f:( + ) ~g:(fun b c -> c - b) ~h:( - ))
let fsub a b c = Float.(Cell.ternary a b c ~f:( - ) ~g:( + ) ~h:(fun c a -> a - c))
let fmult a b c = Float.(Cell.ternary a b c ~f:( * ) ~g:(fun b c -> c / b) ~h:( / ))
let fdiv a b c = Float.(Cell.ternary a b c ~f:( / ) ~g:( * ) ~h:(fun c a -> a / c))

let%expect_test "fneg" =
  let a = Cell.create ~equal:Float.equal in
  let b = Cell.create ~equal:Float.equal in
  fneg a b;
  Cell.update a 5.;
  Cell.query b |> [%sexp_of: float option] |> print_s;
  [%expect {| (-5) |}]
;;

let%expect_test "fadd" =
  let a = Cell.create ~equal:Float.equal in
  let b = Cell.create ~equal:Float.equal in
  let c = Cell.create ~equal:Float.equal in
  fadd a b c;
  Cell.update a 5.;
  Cell.query b |> [%sexp_of: float option] |> print_s;
  Cell.update c 3.5;
  Cell.query b |> [%sexp_of: float option] |> print_s;
  [%expect {|
    ()
    (-1.5) |}]
;;

let%expect_test _ =
  let a = Cell.create ~equal:Float.equal in
  let b = Cell.create ~equal:Float.equal in
  let c = Cell.create ~equal:Float.equal in
  let d = Cell.create ~equal:Float.equal in
  fmult a b c;
  Cell.update a 5.;
  Cell.query b |> [%sexp_of: float option] |> print_s;
  Cell.update c 3.5;
  Cell.query b |> [%sexp_of: float option] |> print_s;
  fneg b d;
  Cell.query d |> [%sexp_of: float option] |> print_s;
  [%expect {|
    ()
    (0.7)
    (-0.7) |}]
;;

(*
(* An ideal interface might look something like this but how do we keep
 * types nicely polymorphic while constraining them to Semilattices? *)
module type Semilattice = sig
  type t [@@deriving equal]

  (* laws:
     * - associativity: meet x (meet y z) = meet (meet x y) z
     * - commutativity: meet x y = meet y x
     * - idempotency:   meet x x = x
     * *)
  val meet : t -> t -> t
end

module Cell(S: Semilattice) = struct
  (* ... *)
end
 *)
