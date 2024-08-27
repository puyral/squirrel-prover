open Ppx_yojson_conv_lib.Yojson_conv.Primitives

type lts_t = LowTraceSequent.t

type cv_parameters = {
  num_retry : int;  (** number of retries*)
  timeout : int;  (** timeout for each solvers*)
}
[@@deriving yojson_of]
(** paramerters to be passed on to cv *)
let yojson_of_cv_parameters x = Utils.Json.to_assoc (yojson_of_cv_parameters x)

let default_parameters = { num_retry = 5; timeout = 1 }

let yojson_of_lts_t s = JsonExport.json_of_low_trace_sequent s

type to_cv = { parameters : cv_parameters; context : lts_t }
[@@deriving yojson_of]

let yojson_of_to_cv x = Utils.Json.to_assoc (yojson_of_to_cv x)

let run_cryptovampire (parameters : cv_parameters) (s : LowTraceSequent.t) =
  let json = yojson_of_to_cv { context=s; parameters } in

  (* print to file *)
  let file = "/tmp/sq.json" in
  let oc = open_out_gen [ Open_creat; Open_trunc; Open_wronly ] 0o777 file in
  let ppf = Format.formatter_of_out_channel oc in
  Format.fprintf ppf "%s@." (Yojson.Safe.pretty_to_string json);
  Format.printf "outputed to %s@\n" file;
  close_out oc;

  (* give up for now *)
  Error "running CryptoVampire is not implemented yet"

module L = Location
module TA = TacticsArgs

(** parse the arguments for the `cryptovampire` tactic *)
let parse_args =
  let aux acc = function
    (* ~nt=[x] for num of retry *)
    | TA.NList ({ L.pl_desc = "nt" }, [ { L.pl_desc = nt } ]) -> (
        match int_of_string_opt nt with
        | Some nt -> { acc with num_retry = nt }
        | None ->
            Tactics.(
              hard_failure (Failure (Printf.sprintf "%s in not a number" nt))))
    (* ~t=[x] for timeout *)
    | TA.NList ({ L.pl_desc = "t" }, [ { L.pl_desc = nt } ]) -> (
        match int_of_string_opt nt with
        | Some nt -> { acc with timeout = nt }
        | None ->
            Tactics.(
              hard_failure (Failure (Printf.sprintf "%s in not a number" nt))))
    | _ -> Tactics.(hard_failure (Failure "unrecognized argument"))
  in
  List.fold_left aux default_parameters

(* register the tactic *)
let () =
  ProverTactics.register_general "cryptovampire" ~pq_sound:false
    (* ^^^^^^^^^^^^ don't know if cv is post-quantum safe, so I'll assume it's not *)
    (fun args s sk fk ->
      let args =
        match args with
        | [ Named_args args ] -> args
        | [] -> []
        | _ -> assert false
      in
      let s =
        match s with
        | Goal.Global _ ->
            Tactics.(
              hard_failure
                (Failure "CryptoVampire doesn't support global goals"))
        | Goal.Local s -> s
      in
      let parameters = parse_args args in
      match run_cryptovampire parameters s with
      | Ok () -> sk [] fk
      | Error e -> fk (None, Tactics.Failure e))
