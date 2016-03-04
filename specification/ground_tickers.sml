structure ground_tickers :> ground_tickers =
struct

open HolKernel boolLib testEval

(* code to take a list of theorems and instantiate variables so as to satisfy
   constraints in the hypotheses, thereby eliminating them.  Result should
   be a list of theorems without hypotheses of the form

     h0  -- label0 --> h1
     h1  -- label1 --> h2
     ...
*)

val w32_max = Arbnum.fromString "4294967296"
val w32_maxi = Arbint.fromNat w32_max
val hz : Arbrat.rat =
    Arbrat.fromString
             (term_to_string (rhs (concl TCP1_paramsTheory.HZ_def)))

val ticks_of_t = ``TCP1_timers$ticks_of``
val srange_t = ``TCP1_rangeAnalysis$srange``
val Ticker_t = ``TCP1_timers$Ticker``
val tickintvlmin_t =
    rhs (concl (SIMP_CONV phase2_ss [] ``TCP1_params$tickintvlmin``))
val tickintvlmax_t =
    rhs (concl (SIMP_CONV phase2_ss [] ``TCP1_params$tickintvlmax``))
val Time_Pass_ticker_t = ``TCP1_timers$Time_Pass_ticker``
val Tstamp_t = ``TCP1_baseTypes$Tstamp``
val Tstamp_ty = ``:TCP1_baseTypes$tstamp``
fun mk_seq32 ty = Term.inst [alpha |-> ty]
                            (prim_mk_const {Thy = "TCP1_baseTypes",
                                            Name = "SEQ32"})
fun mk_tstamp t = list_mk_comb(mk_seq32 Tstamp_ty, [Tstamp_t, t])
fun mk_n2w32 t = mk_comb(``word32$n2w``, t)

fun rat_to_term r = let
  open realSyntax Arbrat
in
  if denominator r = Arbnum.one then term_of_int (numerator r)
  else mk_div(term_of_int (numerator r),
              term_of_int (Arbint.fromNat (denominator r)))
end
fun mk_ticker(tstamp_t, remdr_t) = let
  open pairSyntax
in
  mk_comb(Ticker_t,
          list_mk_pair[tstamp_t, remdr_t, tickintvlmin_t, tickintvlmax_t])
end

fun mk_ticker_from_tickremdr (tickcount,remdr) = let
  val tstamp_t = mk_tstamp (mk_n2w32 (numSyntax.mk_numeral tickcount))
  val remdr_t = rat_to_term remdr
  val mkpair = pairSyntax.list_mk_pair
in
  mk_ticker(tstamp_t, remdr_t)
end

val zeroseq = mk_tstamp (mk_n2w32 (numSyntax.mk_numeral Arbnum.zero))

fun seq_to_arbnum t =
    numSyntax.dest_numeral (rand (rand t))

fun time_to_tickremdr (t:Arbrat.rat) = let
  open Arbrat
  val flr = floor (t * hz)
  val c = Arbint.mod(flr, w32_maxi)
in
  (Arbint.toNat c, t - fromAInt flr / hz)
end

fun tickremdr_to_time (n,r) = let
  open Arbrat
in
  (fromNat n / hz) + r
end

fun load_tstamp_db (db, t) =
    if is_eq t andalso same_const (rator (lhs t)) ticks_of_t then let
        val k = rand (lhs t)
        val v = seq_to_arbnum (rhs t)
      in
        Binarymap.insert(db,k,v)
      end
    else db

fun time_addition(t0,dur) =
    time_to_tickremdr (Arbrat.+(tickremdr_to_time t0, dur))

fun time_subtraction(t0,dur) =
    time_to_tickremdr (Arbrat.-(tickremdr_to_time t0, dur))

fun dur_to_rat dur = let
  open realSyntax Arbrat
  val (n,d) = (int_of_term ## int_of_term) (realSyntax.dest_div dur)
in
  fromAInt n /  fromAInt d
end handle HOL_ERR _ => Arbrat.fromAInt (realSyntax.int_of_term dur)
val tickmax_r = dur_to_rat tickintvlmax_t

fun time_passage_db (db, t) = let
  (* t is a Time_Pass_ticker term *)
  val (_, [dur, t1, t2]) = strip_comb t
  val dur_r = dur_to_rat dur
in
  case (Binarymap.peek(db,t1), Binarymap.peek(db,t2)) of
    (NONE, NONE) => NONE
  | (SOME v, NONE) => SOME (Binarymap.insert(db,t2,time_addition(v,dur_r)))
  | (NONE, SOME v) => SOME (Binarymap.insert(db,t1,time_subtraction(v,dur_r)))
  | (SOME v1, SOME v2) => (print "Not checking Time Passage outside logic\n";
                           SOME db)
end

exception Unproductive of term list
fun do_time_passage (db, tocheck, unproductive, dealtwith) =
    case tocheck of
      [] => if null dealtwith then
              if null unproductive then db
              else raise Unproductive unproductive
            else do_time_passage (db, unproductive, [], [])
    | t::ts => let
      in
        case time_passage_db (db, t) of
          NONE => do_time_passage(db, ts, t::unproductive, dealtwith)
        | SOME db' => do_time_passage(db', ts, unproductive, t::dealtwith)
      end

fun return_instantiations db = let
  fun foldthis (k,v,acc) = let
    val ticker = mk_ticker_from_tickremdr v
  in
    #1 (match_term k ticker) @ acc
  end
in
  Binarymap.foldl foldthis [] db
end

fun seqsub l r = let
  open Arbnum
in
  if l >= r then l - r
  else l + w32_max - r
end


fun solve_delta t = let
  open numSyntax
  val (delta_v, body) = dest_exists t
  val lastconj = last (strip_conj body)
  val (l,sum) = dest_eq lastconj
  val l_num = rand (rand l)
  val r_num = rand (rand (rand (rator sum)))
  val candidate = mk_numeral (seqsub (dest_numeral l_num) (dest_numeral r_num))
  val body' = subst [delta_v |-> candidate] body
  val body'_th = SIMP_CONV phase2_ss [] body'
in
  EQT_INTRO (EXISTS (t, candidate) (EQT_ELIM body'_th))
end

fun get_next pass_terms cur = let
  fun findpred t = aconv (List.nth (#2 (strip_comb t), 1)) cur
in
  case List.find findpred pass_terms of
    NONE => NONE
  | SOME tpt => let
      val (_, [dur, _, newtick]) = strip_comb tpt
    in
      SOME (newtick, dur_to_rat dur)
    end
end

fun sort_in_accordance alist blist btoa = let
  val cmp = measure_cmp (fn b => index (equal (btoa b)) alist)
in
  Listsort.sort cmp blist
end


fun time_analyse_hyps hyplist = let
  val db = Binarymap.mkDict Term.compare
  fun foldthis (t, (db,passage_terms)) =
      if same_const (#1 (strip_comb t)) Time_Pass_ticker_t then
        (db,t::passage_terms)
      else (load_tstamp_db (db, t), passage_terms)
  val (db, passage_terms) = List.foldl foldthis (db,[]) hyplist
  fun pass_to_pair t = let val (_,[_,t1,t2]) = strip_comb t in (t1,t2) end
  val tick_pairs = map pass_to_pair passage_terms
  val ordered_ticks = Chaining.norman_hardy Term.compare tick_pairs
  fun calculate_gaps (low as (low_t, low_n)) dur acc current = let
    open Arbrat
    fun cont low dur acc =
        case get_next passage_terms current of
          NONE => acc
        | SOME(next, next_dur) =>
          calculate_gaps low (dur + next_dur) acc next
  in
    if aconv current low_t then cont low dur acc
    else
      case Binarymap.peek (db, current) of
        NONE => cont low dur acc
      | SOME n => let
          val delta = seqsub n low_n
        in
          cont (current, n) zero ({lotick = low_t, hitick = current,
                                   delta = delta, dur = dur} :: acc)
        end
  end
  fun findstart list =
      case list of
        [] => NONE
      | h :: t => let
        in
          case Binarymap.peek (db, h) of
            NONE => findstart t
          | SOME n => SOME (h, n)
        end
  val (first_remdr, first_tick, first_seq) =
      case findstart ordered_ticks of
        SOME start => let
          val gaps = calculate_gaps start Arbrat.zero [] (#1 start)
        in
          case gaps of
            [] => let
              (* there is just one ticks_of equals constraint, so we can
                 assume a rate of 1, and work back to the first tick in the
                 sequence by subtracting *)
              fun pfx_until P [] = []
                | pfx_until P (h::t) = if P h then [h]
                                       else h :: pfx_until P t
              val pfx = pfx_until (equal (#1 start)) ordered_ticks
              val pfx_back = List.rev pfx
              fun lookback (acc as (curr, currtime)) pfx =
                  case pfx of
                    [] => acc
                  | t :: ts => let
                      val (_, delta) = valOf (get_next passage_terms t)
                    in
                      lookback (t, Arbrat.+(currtime,delta)) ts
                    end
              val (tick1, delta) = lookback (#1 start, Arbrat.zero)
                                            (tl pfx_back)
              val start_time = tickremdr_to_time(#2 start, Arbrat.zero)
              val tick1_time = Arbrat.-(start_time, delta)
              val (seq,remdr) = time_to_tickremdr tick1_time
            in
              (remdr, tick1, seq)
            end
          | _ => let
              fun check_rates rate net acc gaps =
                  case gaps of
                    [] => acc
                  | {delta,dur,hitick,lotick} :: rest => let
                      open Arbrat
                      val net' = net + dur - fromNat delta * rate
                    in
                      check_rates rate net' (net'::acc) rest
                    end
              val rates1 = check_rates (Arbrat.inv (Arbrat.fromInt 100))
                                       Arbrat.zero [] (List.rev gaps)
              open Arbrat
              val minr = List.foldl min (hd rates1) (tl rates1)
              val maxr = List.foldl max (hd rates1) (tl rates1)
              val _ =
                  (abs minr <= tickmax_r andalso abs maxr <= tickmax_r andalso
                   maxr - minr <= tickmax_r) orelse
                  raise Fail ("Can't do it with tick rate of "^toString hz^
                              " Hz")
              val first_tick = #lotick (last gaps)
            in
              ((if minr < zero then abs minr else zero), first_tick,
               Binarymap.find(db, first_tick))
            end
        end
      | NONE => (Arbrat.zero, hd ordered_ticks, Arbnum.zero)

  val passdb = Binarymap.mkDict Term.compare
  val passdb = Binarymap.insert(passdb, first_tick,
                                (first_seq, first_remdr))
  val passage_terms' =
      sort_in_accordance ordered_ticks passage_terms
                         (fn t => List.nth(#2 (strip_comb t), 1))

  val passdb = do_time_passage (passdb, passage_terms, [], [])
  val db_insts = return_instantiations passdb
  val insted_terms = map (subst db_insts) passage_terms'
  fun check_passage t =
      (SIMP_CONV (srw_ss()) [TCP1_timersTheory.Time_Pass_ticker_def,
                             LET_DEF] THENC
       solve_delta) t
  val useful_passages = map (EQT_ELIM o check_passage) insted_terms
in
  (db_insts, useful_passages)
end


end (* struct *)