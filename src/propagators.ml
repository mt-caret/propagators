open Core_kernel

module CellState = struct
  type 'a t =
    | Unknown
    | Known of 'a
    | Contradiction

  let map ~f = function
    | Unknown -> Unknown
    | Known x -> Known (f x)
    | Contradiction -> Contradiction
  ;;
end

module Cell = struct
  type opaque_t = Opaque : 'a t -> opaque_t

  and 'a t =
    { mutable state : 'a CellState.t
    ; mutable triggers : (opaque_t * ('a CellState.t -> unit)) list
    }

  let create () = { state = Unknown; triggers = [] }

  let update_internal (t : 'a t) (new_state : 'a CellState.t) ?caller ~equal =
    match t.state, new_state with
    | Unknown, Unknown | Contradiction, _ | _, Contradiction -> ()
    | Known x, Known y when equal x y -> ()
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

  let update t a ~equal = update_internal t (Known a) ~caller:None ~equal

  let query t =
    match t.state with
    | Unknown -> None
    | Contradiction -> None
    | Known x -> Some x
  ;;

  let add_trigger t t' ~f = t.triggers <- (Opaque t', f) :: t.triggers

  let binary (a : 'a t) (b : 'b t) ~(f : 'a -> 'b) ~(g : 'b -> 'a) ~equal_a ~equal_b =
    add_trigger a b ~f:(fun new_state ->
        update_internal b (CellState.map ~f new_state) ~caller:a ~equal:equal_a);
    add_trigger b a ~f:(fun new_state ->
        update_internal a (CellState.map ~f:g new_state) ~caller:b ~equal:equal_b)
  ;;
end

let fneg a b =
  Cell.binary a b ~f:Float.neg ~g:Float.neg ~equal_a:Float.equal ~equal_b:Float.equal
;;
