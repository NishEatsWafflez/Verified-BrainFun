include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"
include "triviallemmas.dfy"

module Lemmas{
    import opened Common 
    import opened Steps
    import opened Equivalence
    import opened Trivial

    lemma ForAllStep(p: Program, res: seq<int>)
      requires changes_correct(p, res)
      requires forall d:: 0 <= d < |res| ==> 0<= res[d] < |p.commands|
      requires sub_changes_1_step(p, res)
      ensures forall d:: (d in res && !(p.commands[d] in ['+', '-', '<', '>'])) ==> next_step(p, d, 1, res)
    {
      assert forall d :: 0 <= d < |res| ==> !(p.commands[res[d]] in ['+', '-', '>', '<']) ==> (res[d]+1 == |p.commands| || (res[d]+1 < |p.commands| && res[d]+1 in res));
      IndexedImpliesMembership(res);
    }

    lemma testingChangeHelper(p: Program, i: int, res: seq<int>)
      requires 0 <= i <= |p.commands|
      decreases |p.commands|-i
      requires res == ChangesHelper(p, i)
      ensures (i == |p.commands| ==> !(i in res))
      {
        if i == |p.commands|{
          assert res == [];
          assert !(i in res);
        }

      }
    lemma ReplacingJumpProperties(ir1: seq<Instr>, ir2: seq<Instr>, i: int, commands: seq<Instr>)
    requires 0<=i < |ir1|
    requires ir1[i] == Jump(0, true)
    requires ir2 == ir1[..i] + [Jump(|commands|-1, true)] + ir1[i+1..]
    ensures |ir1| == |ir2|
    ensures forall k:: 0<= k < |ir1| && k!=i ==> ir1[k]==ir2[k]
    ensures match ir1[i]
            case Jump(_, true) => true
            case _ => false
    ensures match ir2[i]
          case Jump(_, true) => true
          case _ => false
    {}
    

    lemma ReplacingJumpWithJump(p: Program, ir1: seq<Instr>, ir2: seq<Instr>, i: int, next_command_indices: seq<int>, j: int)
      requires |ir1| == |ir2|
      requires 0 <= i < |ir1|
      requires forall k:: 0<= k < |ir1| && k!=i ==> ir1[k]==ir2[k]
      requires match ir1[i]
              case Jump(_, true) => true
              case _ => false
      requires match ir2[i]
            case Jump(_, true) => true
            case _ => false
      requires next_command_indices == Changes(p)
      requires changes_correct(p, next_command_indices)
      requires valid_program(p)
      requires 0 <= j <= |next_command_indices|
      requires 0 <= j <= |ir1|
      requires matched_forall_loop(p, ir1, next_command_indices, j)
      ensures matched_forall_loop(p, ir2, next_command_indices, j)
      {}
    lemma ReplacingEndJumpWithJump(p: Program, ir1: seq<Instr>, ir2: seq<Instr>, i: int, next_command_indices: seq<int>, j: int)
      requires |ir1| == |ir2|
      requires 0 <= i < |ir1|
      requires forall k:: 0<= k < |ir1| && k!=i ==> ir1[k]==ir2[k]
      requires match ir1[i]
              case Jump(_, false) => true
              case _ => false
      requires match ir2[i]
            case Jump(_, false) => true
            case _ => false
      requires next_command_indices == Changes(p)
      requires changes_correct(p, next_command_indices)
      requires valid_program(p)
      requires 0 <= j <= |next_command_indices|
      requires 0 <= j <= |ir1|
      requires matched_forall_loop(p, ir1, next_command_indices, j)

      {}

    lemma ZeroAndRest(p: Program, i: int, res: seq<int>, temp: seq<int>)
    requires 0 <= i < |p.commands|
    requires |res| > 0
    requires res[0]==i
    requires forall d:: d in res ==> 0<=d < |p.commands|
    requires temp == ChangesHelper(p, i+1)
    requires change_helper_correct(p, i+1, temp)
    requires temp == res[1..]
    requires !(p.commands[i] in ['+', '-', '>', '<'])
    requires (forall d:: (d in res[1..] && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands|) || d+1 in res[1..]))
    requires (!(p.commands[res[0]] in ['+', '-', '<', '>'])) ==> res[0] + 1 == |p.commands| || res[0]+1 in temp
    ensures (forall d:: (d in res && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands| && !(d+1 in res)) || (d+1 < |p.commands| && d+1 in res)))
    {
      forall d| d in res
      ensures !(p.commands[d] in ['+', '-', '<', '>']) ==> ((d+1 == |p.commands| && !(d+1 in res)) || (d+1 < |p.commands| && d+1 in res))
      {
        if d in res[1..]{
          if !(p.commands[d] in ['+', '-', '<', '>']){
            assert ((d+1 == |p.commands|) || d+1 in res[1..]);
            assert ((d+1 == |p.commands|) || d+1 in res);
          }
        }
        else if d == res[0]{
          if !(p.commands[d] in ['+', '-', '<', '>']){
            assert ((d+1 == |p.commands|) || d+1 in temp);
            assert ((d+1 == |p.commands|) || d+1 in res[1..]);
            assert ((d+1 == |p.commands|) || d+1 in res);
          }
        }
      }
    }

    lemma ZeroAndRestBigStep(p: Program, i: int, res: seq<int>, temp: seq<int>, k:int)
    requires 0 <= i < |p.commands|
    requires |res| > 0
    requires res[0]==i
    requires k == count_consecutive_symbols(p, i)
    requires temp == ChangesHelper(p, i+k)
    requires change_helper_correct(p, i+k, temp)
    requires temp == res[1..]
    requires (p.commands[i] in ['+', '-', '>', '<'])
    requires (forall d:: (d in res[1..] && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res[1..]))
    requires ((p.commands[res[0]] in ['+', '-', '<', '>'])) ==> res[0] + k == |p.commands| || res[0]+k in temp
     ensures (forall d:: (d in res && (p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+count_consecutive_symbols(p, d) == |p.commands| && !(d+count_consecutive_symbols(p, d) in res)) || (d+count_consecutive_symbols(p, d) < |p.commands| && d+count_consecutive_symbols(p, d) in res)))
    {
      forall d| d in res
      ensures (p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands| && !(d+count_consecutive_symbols(p, d) in res)) || (d+count_consecutive_symbols(p, d) < |p.commands| && d+count_consecutive_symbols(p, d) in res))
      {
        if d in res[1..]{
          if (p.commands[d] in ['+', '-', '<', '>']){
            assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res[1..]);
            assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res);
          }
        }
        else if d == res[0]{
          if (p.commands[d] in ['+', '-', '<', '>']){
            assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in temp);
            assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res[1..]);
            assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res);
          }
        }
      }
    }

    lemma SubArrayPreservesChanges(p: Program, i: int, res: seq<int>, temp: seq<int>)
    requires 0 <= i < |p.commands|
    requires |res| > 0
    requires res[0]==i
    requires temp == ChangesHelper(p, i+1)
    requires change_helper_correct(p, i+1, temp)
    requires temp == res[1..]
    requires (forall d:: (d in temp && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in temp))
    requires !(p.commands[i] in ['+', '-', '>', '<'])
    ensures forall d:: d in res ==> (p.commands[d] in ['+', '-', '<', '>'] ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res))
    {
      forall d | d in res
      ensures p.commands[d] in ['+', '-', '<', '>'] ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res)
      {
        if d in res[1..] && p.commands[d] in ['+', '-', '<', '>']{
          // assume false;
          assert d in temp;
          assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in temp);
          assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res[1..]);
          assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res);
        }else if d in res[1..]{
          assert !(p.commands[d] in ['+', '-', '<', '>']);
        }else{
          assert d == res[0];
          assert res[0] == i;
          assert !(p.commands[i] in ['+', '-', '<', '>']);
          assert !(p.commands[d] in ['+', '-', '<', '>']);          
          // assume false;
        }
      }
    }

    lemma ChangeHelperRecursive(p: Program, i: int, res: seq<int>, temp: seq<int>)
    requires 0 <= i < |p.commands|
    requires |res| > 0
    requires res[0]==i
    requires temp == ChangesHelper(p, i+1)
    requires change_helper_correct(p, i+1, temp)
    requires temp == res[1..]
    requires !(p.commands[i] in ['+', '-', '>', '<'])
    ensures change_helper_correct(p, i, res)
    {
      if |temp| > 0{
        assert temp[0] == i+1;
        assert res[1] == i+1;
      }

      assert (forall d:: (d in temp && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands| && !(d+1 in temp)) || (d+1 < |p.commands| && d+1 in temp)));
      assert (forall d:: (d in res[1..] && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands|) || d+1 in res[1..]));
      assert (!(p.commands[res[0]] in ['+', '-', '<', '>'])) ==> res[0] + 1 == |p.commands| || res[0]+1 in temp;
      ZeroAndRest(p, i, res, temp);
      assert (forall d:: (d in res && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands| && !(d+1 in res)) || (d+1 < |p.commands| && d+1 in res)));
      assert (forall d:: (0<= d <|temp|-1 && !(p.commands[temp[d]] in ['+', '-', '<', '>']))==> (temp[d+1]-temp[d] ==1));
      assert (forall d:: (0<= d <|res|-1 && !(p.commands[res[d]] in ['+', '-', '<', '>']))==> (res[d+1]-res[d] ==1));
      assert (forall d:: 0 <= d < |temp|-1 && p.commands[temp[d]] in ['+', '-', '<', '>'] ==> (temp[d+1]==temp[d]+ count_consecutive_symbols(p, temp[d]) && ((p.commands[temp[d]]!=p.commands[temp[d+1]]))));
      assert (forall d:: 0 <= d < |res|-1 && p.commands[res[d]] in ['+', '-', '<', '>'] ==> (res[d+1]==res[d]+ count_consecutive_symbols(p, res[d]) && ((p.commands[res[d]]!=p.commands[res[d+1]]))));

      assert (forall d:: (d in temp && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in temp));
      // TODO: fix from here, i think the else case is probably wrong? and maybe put the if case in a lemma :)
      SubArrayPreservesChanges(p, i, res, temp);
      // forall d | d in res
      // ensures p.commands[d] in ['+', '-', '<', '>'] ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res)
      // {
      //   if d in res[1..] && p.commands[d] in ['+', '-', '<', '>']{
      //     assume false;
      //     assert d in temp;
      //     assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in temp);
      //     assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res[1..]);
      //     assert ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res);
      //   }else if d in res[1..]{
      //     assert !(p.commands[d] in ['+', '-', '<', '>']);
      //   }else{
      //     assert d == res[0];
      //     assert res[0] == i;
      //     assert !(p.commands[i] in ['+', '-', '<', '>']);
      //     assert !(p.commands[d] in ['+', '-', '<', '>']);          
      //     // assume false;
      //   }
      // }

      assert (forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res));

      assert i+1 == |p.commands| || i+1 in temp;
      // ChangesHelperMerge(p, i, res);

      // assert temp == res[1..];

      assert change_helper_correct(p, i, res);        
    }
    lemma BigStepHelper(p: Program, i: int, res: seq<int>, temp: seq<int>, k: int)
    requires 0 <= i < |p.commands|
    requires |res| > 0
    requires res[0]==i
    requires k == count_consecutive_symbols(p, i)
    requires temp == ChangesHelper(p, i+k)
    requires change_helper_correct(p, i+k, temp)
    requires temp == res[1..]
    requires (p.commands[i] in ['+', '-', '>', '<'])
    requires (forall d:: (0<= d <|temp|-1 && !(p.commands[temp[d]] in ['+', '-', '<', '>']))==> (temp[d+1]-temp[d] ==1))
    ensures forall d:: (0<= d < |res|-1 && !(p.commands[res[d]] in ['+', '-', '<', '>'])) ==> (res[d+1]-res[d]==1)
    {
      forall d | 0 <= d < |res|-1
        ensures !(p.commands[res[d]] in ['+', '-', '<', '>']) ==> (res[d+1]-res[d]==1)
      {
        if d==0{
          assert p.commands[res[d]] in ['+', '-', '<', '>'];
        }else{
          assert temp == res[1..];
          assert temp[d-1]==res[d];
          assert !(p.commands[temp[d-1]] in ['+', '-', '<', '>'])==> (temp[d]-temp[d-1] ==1);
          assert !(p.commands[res[d]] in ['+', '-', '<', '>']) ==> (res[d+1]-res[d]==1);
        }
      }
    }

    lemma ChangeHelperRecursiveBigStep(p: Program, i: int, res: seq<int>, temp: seq<int>, k: int)
    requires 0 <= i < |p.commands|
    requires |res| > 0
    requires res[0]==i
    requires k == count_consecutive_symbols(p, i)
    requires temp == ChangesHelper(p, i+k)
    requires change_helper_correct(p, i+k, temp)
    requires temp == res[1..]
    requires (p.commands[i] in ['+', '-', '>', '<'])
    ensures change_helper_correct(p, i, res)
    {
      if |temp| > 0{
        assert temp[0] == i+k;
        assert res[1] == i+k;
        assert res[1] != res[0];
      }
      assert (forall d:: (d in temp && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in temp));
      assert (forall d:: (d in res[1..] && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res[1..]));
      assert ((p.commands[res[0]] in ['+', '-', '<', '>'])) ==> res[0] + k == |p.commands| || res[0]+k in temp;
      ZeroAndRestBigStep(p, i, res, temp, k);
      assert (forall d:: (d in res && (p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+count_consecutive_symbols(p, d) == |p.commands| && !(d+count_consecutive_symbols(p, d) in res)) || (d+count_consecutive_symbols(p, d) < |p.commands| && d+count_consecutive_symbols(p, d) in res)));

      assert (forall d:: (0<= d <|temp|-1 && !(p.commands[temp[d]] in ['+', '-', '<', '>']))==> (temp[d+1]-temp[d] ==1));
      BigStepHelper(p, i, res, temp, k);
      assert (forall d:: (0<= d <|res|-1 && !(p.commands[res[d]] in ['+', '-', '<', '>']))==> (res[d+1]-res[d] ==1));
      assert (forall d:: 0 <= d < |temp|-1 && p.commands[temp[d]] in ['+', '-', '<', '>'] ==> (temp[d+1]==temp[d]+ count_consecutive_symbols(p, temp[d]) && ((p.commands[temp[d]]!=p.commands[temp[d+1]]))));
      assert (forall d:: 0 <= d < |res|-1 && p.commands[res[d]] in ['+', '-', '<', '>'] ==> (res[d+1]==res[d]+ count_consecutive_symbols(p, res[d]) && ((p.commands[res[d]]!=p.commands[res[d+1]]))));
      assert (forall d:: (d in temp && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands|) || d+1 in temp));
      
      forall d | d in res
      ensures !(p.commands[d] in ['+', '-', '<', '>']) ==> ((d+1 == |p.commands| && !(d+1 in res)) || (d+1 < |p.commands| && d+1 in res))
      {
        if d in res[1..]{
          assert d in temp;
          assert !(p.commands[d] in ['+', '-', '<', '>']) ==> ((d+1 == |p.commands| && !(d+1 in temp)) || (d+1 < |p.commands| && d+1 in temp));
          assert !(p.commands[d] in ['+', '-', '<', '>']) ==> ((d+1 == |p.commands| && !(d+1 in res[1..])) || (d+1 < |p.commands| && d+1 in res[1..]));
          assert !(p.commands[d] in ['+', '-', '<', '>']) ==> ((d+1 == |p.commands| && !(d+1 in res)) || (d+1 < |p.commands| && d+1 in res));
        }else{
          assert (p.commands[d] in ['+', '-', '<', '>']);
        }
      }

      assert (forall d:: (d in res && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands| && !(d+1 in res)) || (d+1 < |p.commands| && d+1 in res)));
      // assert i+1 == |p.commands| || i+1 in temp;
      // ChangesHelperMerge(p, i, res);

      // assert temp == res[1..];

      assert change_helper_correct(p, i, res);        
    }




    lemma ChangeHelperLemma(p: Program, i: int, res: seq<int>)
      requires 0 <= i <= |p.commands|
      decreases |p.commands|-i
      requires res == ChangesHelper(p, i)
      ensures change_helper_correct(p, i, res)
    {
      if i == |p.commands|{
        assert res == [];
        assert !(i in res);
        assert change_helper_correct(p, i, res);

      }
      else if i < |p.commands| && p.commands[i] in ['+', '-', '<', '>']{
        assert res[0] == i;
        var k := count_consecutive_symbols(p, i);
        var temp := ChangesHelper(p, i+k);
        ChangeHelperLemma(p, i+k, temp);
        assert change_helper_correct(p, i+k, temp);
        ChangeHelperRecursiveBigStep(p, i, res, temp, k);
        assert change_helper_correct(p, i, res);
        // assert (forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) >= |p.commands|) || d+count_consecutive_symbols(p, d) in res));

        // (forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) >= |p.commands|) || d+count_consecutive_symbols(p, d) in res))
      }else{
        assert res[0] == i;
        var k := 1;
        var temp := ChangesHelper(p, i+k);
        ChangeHelperLemma(p, i+k, temp);
        assert change_helper_correct(p, i+k, temp);
        ChangeHelperRecursive(p, i, res, temp);


        // if |temp| > 0{
        //   assert temp[0] == i+k;
        //   // assert p.commands[temp[0]] != p.commands[i]; 
        // }
        // assert i+k == |p.commands| || i+k in temp;
        // // ChangesHelperMerge(p, i, res);

        // assert temp == res[1..];
        assert change_helper_correct(p, i, res);        // (forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) >= |p.commands|) || d+count_consecutive_symbols(p, d) in res))
      }
      // assert forall d:: 0<= d <|res| ==> 0<= res[d] <|p.commands|;
      // assert forall d:: 0 <= d < |res|-1 && p.commands[res[d]] in ['+', '-', '<', '>'] ==> res[d+1]==res[d]+ count_consecutive_symbols(p, res[d]);
    }
    lemma ChangeLemma(p: Program, res: seq<int>)
    // ensures forall i:: 0<= i< |Changes(p)| ==> 0<= Changes(p)[i] <|p.commands|
    // ensures forall i:: 0 <= i < |Changes(p)|-1 && p.commands[Changes(p)[i]] in ['+', '-', '<', '>'] ==> Changes(p)[i+1]==Changes(p)[i]+ count_consecutive_symbols(p, Changes(p)[i])
    // // ensures forall i:: i in Changes(p) && p.commands[i] in ['+', '-', '<', '>']  && i + count_consecutive_symbols(p, i) < |p.commands|==> i+ count_consecutive_symbols(p, i) in Changes(p)
    // ensures forall d:: 0<= d <|Changes(p)|-1 && p.commands[Changes(p)[d]] in ['+', '-', '<', '>']==> ((p.commands[Changes(p)[d]]!=p.commands[Changes(p)[d+1]]))
    // ensures forall d:: 0<= d <|Changes(p)|-1 && !(p.commands[Changes(p)[d]] in ['+', '-', '<', '>'])==> (Changes(p)[d+1]-Changes(p)[d] ==1)
    // ensures forall d:: (d in Changes(p) && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) >= |p.commands|) || d+count_consecutive_symbols(p, d) in Changes(p))
    // ensures forall d:: (d in Changes(p) && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 >= |p.commands|) || d+1 in Changes(p))
    requires res == Changes(p)
    ensures changes_correct(p, res)
    {
      ChangeHelperLemma(p, 0, res);
      assert change_helper_correct(p, 0, res);
    }



    lemma ForAllHelper(p: Program, res: seq<int>)
    // requires res == Changes(p)
    requires changes_correct(p, res)
    requires forall d:: 0<= d < |res| ==> 0<= res[d] < |p.commands|
    // ensures forall i:: 0<= i< |Changes(p)| ==> 0<= Changes(p)[i] <|p.commands|
    ensures forall i:: 0 <= i < |res|-1 && p.commands[res[i]] in ['+', '-', '<', '>'] ==> (res[i+1]==res[i]+ count_consecutive_symbols(p, res[i]) && (p.commands[res[i]]!=p.commands[res[i+1]]))
    ensures forall d:: 0<= d <|res|-1 && !(p.commands[res[d]] in ['+', '-', '<', '>'])==> (res[d+1]-res[d] ==1)
    ensures forall d :: 0 <= d < |res| ==> !(p.commands[res[d]] in ['+', '-', '>', '<']) ==> (res[d]+1 == |p.commands| || (res[d]+1 < |p.commands| && res[d]+1 in res))
    ensures forall d :: 0 <= d < |res| ==>  (p.commands[res[d]] in ['+', '-', '>', '<']) ==> (res[d]+count_consecutive_symbols(p, res[d]) == |p.commands| || (res[d]+count_consecutive_symbols(p, res[d]) < |p.commands| && res[d]+count_consecutive_symbols(p, res[d]) in res))
      
    // ensures forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res)
    // ensures forall d:: (d in res && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands|) || d+1 in res)
    {  
      assert changes_correct(p, res);
      forall d | 0 <= d < |res|-1
      ensures !(p.commands[res[d]] in ['+', '-', '>', '<']) ==> res[d+1] - res[d] ==1
      ensures p.commands[res[d]] in ['+', '-', '>', '<'] ==> (res[d+1]==res[d]+ count_consecutive_symbols(p, res[d]) && (p.commands[res[d]]!=p.commands[res[d+1]]))
      {
        if !(p.commands[res[d]] in ['+', '-', '>', '<']){
          assert res[d+1]-res[d] ==1;
        }else{
          var k := count_consecutive_symbols(p, res[d]);
          assert res[d+1]==res[d]+ count_consecutive_symbols(p, res[d]) && (p.commands[res[d]]!=p.commands[res[d+1]]);
        }
      }
      forall d | 0 <= d < |res|
      ensures !(p.commands[res[d]] in ['+', '-', '>', '<']) ==> (res[d]+1 == |p.commands| || (res[d]+1 < |p.commands| && res[d]+1 in res))
      ensures (p.commands[res[d]] in ['+', '-', '>', '<']) ==> (res[d]+count_consecutive_symbols(p, res[d]) == |p.commands| || (res[d]+count_consecutive_symbols(p, res[d]) < |p.commands| && res[d]+count_consecutive_symbols(p, res[d]) in res))
      {
        if !(p.commands[res[d]] in ['+', '-', '>', '<']){
          assert res[d]+1 ==|p.commands| || (res[d]+1 < |p.commands| && res[d]+1 in res);
        }else{
          var k := count_consecutive_symbols(p, res[d]);
          assert res[d]+k == |p.commands| || (res[d]+k < |p.commands| && res[d]+k in res);
        }
      }
    }

  lemma AlignmentBackwards(p: Program, s: State, ir: IntermediateRep, i: int, k: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    // requires ir.commands[i]==Move(_)
    requires ir.commands[i] == Move(k)
    requires k < 0
    ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 
  {
    
    var indices := Changes(p);      
    var index := indices[i];
    var currIr := IntermediateRep(ir.commands, i, ir.input);
    assert p.commands[index] in ['>', '<'];
    var p_by_k := Program(p.commands, index, p.input);
    MaxSteps(p_by_k, s);
    assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
    var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
    assert max_steps(p_by_k,s, p', s');
    assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '<'));
    assert index-k < |p.commands| ==> (p.commands[index] != p.commands[index-k]);
    assert forall j:: index <= j < index-k ==> p.commands[j] == p.commands[index]; 
    assert index == p_by_k.pointer;
    assert -p'.pointer + p_by_k.pointer==k;
    IrStep(currIr, s);
    var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
    assert ir_step(currIr, s, ir', sIR);
    if (s.pointer + k >= |s.memory|){
      assert sIR.pointer == |s.memory|-1;
      assert s'.pointer == |s.memory|-1;

    } else if (s.pointer +k < 0){
      assert sIR.pointer == 0;
      assert s'.pointer == 0;
    } else {
      assert sIR.pointer == s.pointer +k;
      assert s'.pointer == s.pointer +k;
    }
    assert sIR.memory == s.memory;
    assert max_steps(p_by_k, s, p', s');
    assert p_by_k.commands[p_by_k.pointer]=='<';
    assert s'.memory==s'.memory;
    assert p'.pointer - p_by_k.pointer==-k;
    assert s'.memory == sIR.memory;
    assert s'.output == s.output;
    assert sIR.output == s.output;
    assert s'.output == sIR.output;
    assert s'.pointer == sIR.pointer; 
    assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
    assert i < |Changes(p)|;
    assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
    assert max_steps(p_by_k, s, p', s');
    assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
    assert program_k_max_steps(p, s, p', s', i);
    assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
    assert sIR == s';
    assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
                      
  }

  lemma AlignmentForwards(p: Program, s: State, ir: IntermediateRep, i: int, k: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    // requires ir.commands[i]==Move(_)
    requires ir.commands[i] == Move(k)
    requires k >= 0
    ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 
  {
    
    var indices := Changes(p);      
    var index := indices[i];
    var currIr := IntermediateRep(ir.commands, i, ir.input);
    assert p.commands[index] in ['>', '<'];
    var p_by_k := Program(p.commands, index, p.input);
    MaxSteps(p_by_k, s);
    assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
    var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
    assert max_steps(p_by_k,s, p', s');
    assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '>'));
    assert index+k < |p.commands| ==> (p.commands[index] != p.commands[index+k]);
    assert forall j:: index <= j < index+k ==> p.commands[j] == p.commands[index]; 
    assert index == p_by_k.pointer;
    assert p'.pointer - p_by_k.pointer==k;
    IrStep(currIr, s);
    var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
    assert ir_step(currIr, s, ir', sIR);
    if (s.pointer + k >= |s.memory|){
      assert sIR.pointer == |s.memory|-1;
      assert s'.pointer == |s.memory|-1;

    } else if (s.pointer +k < 0){
      assert sIR.pointer == 0;
      assert s'.pointer == 0;
    } else {
      assert sIR.pointer == s.pointer +k;
      assert s'.pointer == s.pointer +k;
    }
    assert sIR.memory == s.memory;
    assert max_steps(p_by_k, s, p', s');
    assert p_by_k.commands[p_by_k.pointer]=='>';
    assert s'.memory==s'.memory;
    assert p'.pointer - p_by_k.pointer==k;
    assert s'.memory == sIR.memory;
    assert s'.output == s.output;
    assert sIR.output == s.output;
    assert s'.output == sIR.output;
    assert s'.pointer == sIR.pointer; 
    assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
    assert i < |Changes(p)|;
    assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
    assert max_steps(p_by_k, s, p', s');
    assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
    assert program_k_max_steps(p, s, p', s', i);
    assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
    assert sIR == s';
    assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;    
  }

    lemma AlignmentMeansEquivalenceMoves(p: Program, s: State, ir: IntermediateRep, i: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    // requires ir.commands[i]==Move(_)
    requires match ir.commands[i] {
      case Move(_) => true
      case _ => false
    }    
      ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 
    {
        // ChangeLemma(p);
        // ForAllHelper(p);
        var indices := Changes(p);      
        var index := indices[i];
        var currIr := IntermediateRep(ir.commands, i, ir.input);
        match ir.commands[i] 
          case Move(k) =>{
            assert p.commands[index] in ['>', '<'];
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            if k >= 0{
              AlignmentForwards(p, s, ir, i, k);
            }else{
              AlignmentBackwards(p, s, ir, i, k);                      
            }
          
          }

    }

    lemma AlignmentMeansEquivalenceLoops(p: Program, s: State, ir: IntermediateRep, i: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    requires match ir.commands[i] {
      case Jump(_, _) => true
      case _ => false
    }
    ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 
    {
      var index := Changes(p)[i];
      var currIr := IntermediateRep(ir.commands, i, ir.input);
      var p_by_k := Program(p.commands, index, p.input);
      MaxSteps(p_by_k, s);
      assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
      var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
      assert max_steps(p_by_k,s, p', s');
      IrStep(currIr, s);  

      var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
      // assert sIR.memory == s.memory;
      assert sIR == s;
      assert s'==s;
      assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;

      // assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i);
      // assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input);
      // assert ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);

      assert sIR == s';
    }
    lemma AlignmentDecrement (p: Program, s: State, ir: IntermediateRep, i: int, k: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    requires ir.commands[i] == Inc(k)
    requires k < 0
    ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 

    {
    var indices := Changes(p);      
    var index := indices[i];
    var currIr := IntermediateRep(ir.commands, i, ir.input);
    assert p.commands[index] in ['+', '-'];
    var p_by_k := Program(p.commands, index, p.input);
    MaxSteps(p_by_k, s);
    // assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
    var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
    assert max_steps(p_by_k,s, p', s');
    // assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '-'));
    assert index-k < |p.commands| ==> (p.commands[index] != p.commands[index-k]);
    assert forall j:: index <= j < index-k ==> p.commands[j] == p.commands[index]; 
    assert index == p_by_k.pointer;
    assert -p'.pointer + p_by_k.pointer==k;
    IrStep(currIr, s);
    var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
    assert ir_step(currIr, s, ir', sIR);
    assert s.pointer == sIR.pointer;
    assert s.pointer == s'.pointer;
    assert sIR.memory[sIR.pointer] == (s.memory[sIR.pointer]+k)%256;
    assert max_steps(p_by_k, s, p', s');
    assert p_by_k.commands[p_by_k.pointer]=='-';
    assert s'.memory[s'.pointer] == (s.memory[s.pointer]- p'.pointer+p_by_k.pointer)%256;
    assert p'.pointer - p_by_k.pointer==-k;
    assert s'.memory[s'.pointer] == (s.memory[s.pointer]+k)%256;
    assert s'.memory == sIR.memory;
    assert s'.output == s.output;
    assert sIR.output == s.output;
    assert s'.output == sIR.output;
    assert s'.pointer == sIR.pointer; 
    assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
    assert i < |Changes(p)|;
    assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
    assert max_steps(p_by_k, s, p', s');
    assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
    assert program_k_max_steps(p, s, p', s', i);
    assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
    assert sIR == s';
    assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
    }


    lemma AlignmentIncrement(p: Program, s: State, ir: IntermediateRep, i: int, k: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    requires ir.commands[i] == Inc(k)
    requires k >= 0
    ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 

    {
      var indices := Changes(p);      
      var index := indices[i];
      var currIr := IntermediateRep(ir.commands, i, ir.input);
      assert p.commands[index] in ['+', '-'];
      var p_by_k := Program(p.commands, index, p.input);
      MaxSteps(p_by_k, s);
      assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
      var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
      assert max_steps(p_by_k,s, p', s');
      assert (forall i:: (p_by_k.pointer<=i< p'.pointer ==>  p_by_k.commands[i] == '+'));
      assert index+k < |p.commands| ==> (p.commands[index] != p.commands[index+k]);
      assert forall j:: index <= j < index+k ==> p.commands[j] == p.commands[index]; 
      assert index == p_by_k.pointer;
      assert p'.pointer - p_by_k.pointer==k;
      IrStep(currIr, s);
      var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
      assert ir_step(currIr, s, ir', sIR);
      assert s.pointer == sIR.pointer;
      assert s.pointer == s'.pointer;
      assert sIR.memory[sIR.pointer] == (s.memory[sIR.pointer]+k)%256;
      assert max_steps(p_by_k, s, p', s');
      assert p_by_k.commands[p_by_k.pointer]=='+';
      assert s'.memory[s'.pointer] == (s.memory[s.pointer]+ p'.pointer-p_by_k.pointer)%256;
      assert p'.pointer - p_by_k.pointer==k;
      assert s'.memory[s'.pointer] == (s.memory[s.pointer]+k)%256;
      assert s'.memory == sIR.memory;
      assert s'.output == s.output;
      assert sIR.output == s.output;
      assert s'.output == sIR.output;
      assert s'.pointer == sIR.pointer; 
      assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s');
      assert i < |Changes(p)|;
      assert p_by_k == Program(p.commands, Changes(p)[i], p.input);
      assert max_steps(p_by_k, s, p', s');
      assert max_steps(Program(p.commands, Changes(p)[i], p.input), s, p', s');
      assert program_k_max_steps(p, s, p', s', i);
      assert state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR);
      assert sIR == s';
      assert valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR ;
    }
    lemma AlignmentMeansEquivalenceIncs(p: Program, s: State, ir: IntermediateRep, i: int)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    requires 0 <= i < |ir.commands|
    requires match ir.commands[i] {
      case Inc(_) => true
      case _ => false
    }    
      ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 
    {
        // ChangeLemma(p);
        // ForAllHelper(p);
        var indices := Changes(p);      
        var index := indices[i];
        var currIr := IntermediateRep(ir.commands, i, ir.input);
        match ir.commands[i] 
          case Inc(k) =>{
            assert p.commands[index] in ['+', '-'];
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            if k >= 0{
              AlignmentIncrement(p, s, ir, i, k);
            }else{
              AlignmentDecrement(p, s, ir, i, k);

            }
          
          }

    }


    lemma AlignmentMeansEquivalenceAllStates(p: Program, ir: IntermediateRep)
    requires valid_program(p)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    ensures FullEquivalence(p, ir)
    {
      forall s | state_reqs(s)
      ensures EquivalentReps(p, s, ir)
      {
        AlignmentMeansEquivalence(p, s, ir);
      }
    }

    lemma AlignmentMeansEquivalence(p: Program, s: State, ir: IntermediateRep)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input) 
    requires ir.input == p.input
    requires valid_input(p.input)
    requires aligned_instructions(p, ir)
    ensures EquivalentReps(p, s, ir)
    {
      var indices := Changes(p);      
      forall i | within_ir_range(i, ir)
      ensures exists p': Program, s': State, ir': IntermediateRep, sIR: State:: valid_program(p') && aligned_programs(p, p') && valid_state(s, s') && state_reqs(s')  && program_k_max_steps(p, s, p', s', i) && state_reqs(sIR) && valid_state(s, sIR) && valid_ir(ir') && valid_input(ir'.input) && ir_step(IntermediateRep(ir.commands, i, ir.input), s, ir', sIR) && s'==sIR 

      {

        var index := indices[i];
        var currIr := IntermediateRep(ir.commands, i, ir.input);
        match ir.commands[i] 
          case Inc(k) =>{
            AlignmentMeansEquivalenceIncs(p, s, ir, i);
          } 
          case Move(k) =>{
            AlignmentMeansEquivalenceMoves(p, s, ir, i);          
          }
          case Print =>{
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            IrStep(currIr, s);  
            var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
            assert sIR.memory == s.memory;
            assert sIR == s';          
          }
          case UserInput =>{
            var p_by_k := Program(p.commands, index, p.input);
            MaxSteps(p_by_k, s);
            assert exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            var p': Program, s': State :| valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p_by_k, p') && max_steps(p_by_k, s, p', s')  && valid_input(p'.input);
            assert max_steps(p_by_k,s, p', s');
            IrStep(currIr, s);  
            var ir': IntermediateRep, sIR :|valid_state(s, sIR) && state_reqs(sIR) && in_sync_irs(currIr, ir') && valid_ir(ir') && ir_step(currIr, s, ir', sIR) && valid_input(ir'.input);
            assert sIR == s';          
          }
          case Jump(dest, dir)=>{
            AlignmentMeansEquivalenceLoops(p, s, ir, i);
          }
      }

      assert EquivalentReps(p, s, ir);

    }



lemma IrStep(ir: IntermediateRep, s: State)
    requires state_reqs(s)
    requires valid_input(ir.input)
    requires valid_ir(ir)
    decreases |ir.commands| - ir.pointer //Need to figure out how to prove decreases or termination as we descend into recursion :0
    ensures exists ir': IntermediateRep, s': State :: valid_state(s, s') && state_reqs(s') && in_sync_irs(ir, ir') && valid_ir(ir') && ir_step(ir, s, ir', s') && valid_input(ir'.input)
{
    if ir.pointer == |ir.commands| {
        var ir' := ir;
        var s' := s;
        assert state_reqs(s') && ir_step(ir, s, ir', s');
    }else{
        // assert loop_depth(ir) == 1 ==> (ir.commands[ir.pointer] is Instr);

        match ir.commands[ir.pointer]
            case Inc(n) =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var mem := s.memory;
                mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+n)%256] + mem[s.pointer+1..];
                var s' := StateValue(s.pointer, mem, s.output);
                // assert ir'.commands == ir.commands;
                assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
            }
            case Move(n) =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var pt := s.pointer;
                if pt+n >= |s.memory|{
                    pt := |s.memory|-1;
                }else if pt+n <0{
                    pt := 0;
                }else{
                    pt := pt+n;
                }
                var s' := StateValue(pt, s.memory, s.output);
                assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
                
            }
            case Print =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var s' := StateValue(s.pointer, s.memory, s.output+ [s.memory[s.pointer] as char]);
                assert state_reqs(s') &&valid_state(s, s') && ir_step(ir, s, ir', s');
            }
            case UserInput =>{
                if |ir.input| == 0{
                    var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                    assert ir_moved_up(ir, ir');
                    var mem := s.memory;
                    mem :=   mem[..s.pointer] + [' ' as int] + mem[s.pointer+1..];
                    assert mem[s.pointer] == ' ' as int;
                    var s' := StateValue(s.pointer, mem, s.output);
                    assert s'.memory[s.pointer] == ' ' as int;
                    assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
                } else if |ir.input| > 0{
                    var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input[1..]);
                    assert ir_moved_up(ir, ir');
                    var mem := s.memory;
                    mem :=   mem[..s.pointer] + [ir.input[0] as int] + mem[s.pointer+1..];
                    assert mem[s.pointer] == ir.input[0] as int;
                    var s' := StateValue(s.pointer, mem, s.output);
                    assert s'.memory[s.pointer] == ir.input[0] as int;
                    assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');   
                }
            }
            case Jump(dest, direction) =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                if direction{
                  if s.memory[s.pointer] > 0{
                    ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                  }else{
                    ir' := IntermediateRep(ir.commands, dest+1, ir.input);
                  }
                } else{
                  if s.memory[s.pointer] > 0{
                    ir' := IntermediateRep(ir.commands, dest+1, ir.input);
                  }else{
                    ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                  }
                }
                var s' := s;
                assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');

                // assert state_reqs(s') && valid_state(s, s') && ir_step(ir, s, ir', s');
            }    

            
    }
}

lemma MaxSteps(p: Program, s: State)
  requires 0 <= p.pointer <= |p.commands|
  requires valid_program(p)
  requires state_reqs(s)
  requires valid_input(p.input)
//   requires enough_input(p)
  requires 0 <= s.pointer < |s.memory|
  ensures exists p': Program, s': State ::  valid_program(p') &&  state_reqs(s') &&  valid_state(s, s') &&  aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    
    if p.pointer == |p.commands| {
        var p' := p;
        var s' := s;
        assert (exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s'));

    }else{
    if p.commands[p.pointer] == '+' || p.commands[p.pointer] == '-' {MaxStepsPlusMinus(p, s);}
    else if p.commands[p.pointer] in ['>', '<']{   MaxStepsMove(p, s);}
    else if p.commands[p.pointer] == '.'{   MaxStepsPrint(p, s);}
    else if p.commands[p.pointer] == ','{   
        
        MaxStepsInput(p, s);}
    else if p.commands[p.pointer] == '['{   MaxStepsStartLoop(p, s);}
    else if p.commands[p.pointer] == ']'{   MaxStepsEndLoop(p, s);}
    }
    assert (exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') && valid_input(p'.input));
}

lemma MaxStepsPlusMinus(p: Program, s: State)
  requires 0 <= p.pointer < |p.commands|
  requires valid_program(p)
//   requires enough_input(p)
  requires valid_input(p.input)
  requires state_reqs(s)
  requires p.commands[p.pointer] in ['+', '-']
  requires 0 <= s.pointer < |s.memory|
  ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    var i := p.pointer+1;
    while i < |p.commands| && p.commands[i] ==p.commands[p.pointer]
    decreases |p.commands|-i
    invariant i <= |p.commands|
    invariant forall j:: p.pointer <= j < i ==> p.commands[j] == p.commands[p.pointer]
    {
        i := i+1;
    }
    var mem := s.memory;
    var p' := Program(p.commands, i, p.input);

    if p.commands[p.pointer] == '+'{
      mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+p'.pointer-p.pointer)%256] + mem[s.pointer+1..];
      assert mem[s.pointer] == (s.memory[s.pointer]+p'.pointer-p.pointer)%256;
    }else if p.commands[p.pointer]=='-'{
      mem :=   mem[..s.pointer] + [(s.memory[s.pointer]-p'.pointer+p.pointer)%256] + mem[s.pointer+1..];
      assert mem[s.pointer] == (s.memory[s.pointer]-p'.pointer+p.pointer)%256;


    }
    var s' := StateValue(s.pointer, mem, s.output);
    assert valid_program(p') && aligned_programs(p, p');
    assert state_reqs(s');
    assert (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] ==p.commands[p.pointer]));
    assert (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == p.commands[p.pointer])));
    assert (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i]);
    // assert count == count_commands(p, p', ['+', '-']);
    assert valid_input(p'.input);
    assert p.commands[p.pointer] == '+' ==> s'.memory[s.pointer] == (s.memory[s.pointer]+p'.pointer-p.pointer)%256;
    assert p.commands[p.pointer] == '-'==>(s'.memory[s.pointer] == (s.memory[s.pointer]-p'.pointer+p.pointer)%256);
    assert max_steps(p, s, p', s');
}

lemma MaxStepsPrint(p: Program, s: State)
    requires valid_program(p)
    requires state_reqs(s)
    requires valid_input(p.input)
    requires 0 <= p.pointer < |p.commands|
    requires p.commands[p.pointer] == '.'
    ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    var out := s.output;
    out := out + [s.memory[s.pointer] as char];
    var s' := StateValue(s.pointer, s.memory, out);
    var p' := Program(p.commands, p.pointer+1, p.input);
    assert p'.pointer == p.pointer+1;
    assert p'.commands == p.commands;
    assert pointer_moved_up(p, p');
    assert valid_program(p) && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p) && program_step(s, p, s', p');
    assert max_steps(p, s, p', s');
}

lemma MaxStepsInput(p: Program, s: State)
    requires valid_program(p)
    requires state_reqs(s)
    requires 0 <= p.pointer < |p.commands|
    requires p.commands[p.pointer] == ','

    requires valid_input(p.input)
    ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    var mem := s.memory;
    assert |p.input| >= 0;
    // var newVal := s.memory[s.pointer];
    if |p.input| > 0{
        var p' := Program(p.commands, p.pointer+1, p.input[1..]);
        assert p.input[0] as int <= 255;
        mem :=   mem[..s.pointer] + [p.input[0] as int] + mem[s.pointer+1..];
        var s' := StateValue(s.pointer, mem, s.output);
        assert p'.pointer == p.pointer+1;
        assert p'.commands == p.commands;
        // assert forall j :: p.pointer <= j < i ==> !(j in s2);
        // assert |s2|==0;
        assert pointer_moved_up(p, p');
        assert valid_program(p) && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p) && program_step(s, p, s', p');
        assert max_steps(p, s, p', s');
    }else if |p.input|==0{
        assert |p.input|==0;
        var p' := Program(p.commands, p.pointer+1, p.input);
        mem :=   mem[..s.pointer] + [' ' as int] + mem[s.pointer+1..];
        var s' := StateValue(s.pointer, mem, s.output);
        assert p'.pointer == p.pointer+1;
        assert p'.commands == p.commands;
        // assert forall j :: p.pointer <= j < i ==> !(j in s2);
        // assert |s2|==0;
        assert pointer_moved_up(p, p');
        assert valid_program(p) && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p) && program_step(s, p, s', p');
        assert max_steps(p, s, p', s');
    }

}

lemma ForallElimValidLoop(p: Program, s: State, i: int)
requires valid_program(p)
requires 0<= i < |p.commands|
requires p.commands[i]=='['
ensures exists k::  i< k < |p.commands| && p.commands[k]== ']' && valid_loop(p.commands[i+1..k])
{
  assert valid_loop(p.commands);
  assert forall j:: (0<= j < |p.commands| ==>(
                (p.commands[j]== '[' ==> exists k::  j< k < |p.commands| && p.commands[k]== ']' && valid_loop(p.commands[j+1..k]))
                &&
                (p.commands[j]== ']' ==> exists k::  0<= k < j && p.commands[k]== '[' && valid_loop(p.commands[k+1..j]))
            ));
  assert p.commands[i] == '[';
  assert exists k::  i< k < |p.commands| && p.commands[k]== ']' && valid_loop(p.commands[i+1..k]);
}

lemma EquivalentBodies(p: Program, s: State, k: int, p': Program)
requires valid_program(p)
requires p.pointer< k < |p.commands| && p.commands[k]== ']'
requires valid_loop(p.commands[p.pointer+1..k])
requires k==p'.pointer-1
// requires p.commands[p.pointer+1..k]==p.commands[p.pointer+1..p'.pointer-1]
requires p.commands == p'.commands
ensures valid_loop(p.commands[p.pointer+1..p'.pointer-1])
ensures valid_loop(p'.commands[p.pointer+1..p'.pointer-1])
{
  // if empty_body(p.commands[p.pointer+1..k]){

  // }
  var subarray := p.commands[p.pointer+1..k];
  assert valid_loop(subarray);
  assert subarray == p.commands[p.pointer+1.. p'.pointer-1];
  assert valid_loop(p.commands[p.pointer+1.. p'.pointer-1]);

}

lemma StartLoopStepHelp(p: Program, s: State)
  requires valid_program(p)
  requires state_reqs(s)
  requires 0 <= p.pointer < |p.commands|
  requires p.commands[p.pointer] == '['
  requires valid_input(p.input)
  requires s.memory[s.pointer]==0
  ensures exists p': Program, s': State:: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') && valid_input(p'.input)
  // ensures exists p': Program :: valid_loop(p'.commands[p.pointer+1..p'.pointer-1])
  {
    assert valid_loop(p.commands);
    ForallElimValidLoop(p, s, p.pointer);
    // assert exists k::  p.pointer< k < |p.commands| && p.commands[k]== ']' && valid_loop(p.commands[p.pointer+1..k]);
    var k :| p.pointer< k < |p.commands| && p.commands[k]== ']' && valid_loop(p.commands[p.pointer+1..k]);
    var p' := Program(p.commands, k+1, p.input);
    assert valid_program(p');
    assert k==p'.pointer-1;
    EquivalentBodies(p, s, k, p');
    assert valid_loop(p'.commands[p.pointer+1..p'.pointer-1]);
    assert p'.pointer > k > p.pointer;
    assert p'.commands==p.commands;
    assert p.commands[k]==']';
    assert p'.commands[k]==']';
    assert p'.pointer-1==k;
    EqualIndex(p'.commands, k, p'.pointer);
    assert p'.commands[p'.pointer-1]==p'.commands[k];
    assert p'.commands[p'.pointer-1]== ']';
    assert 0 <= p.pointer < |p.commands| && 0 <= p'.pointer <= |p'.commands| && p.commands == p'.commands;
    assert s.memory[s.pointer]== 0 ==> (p'.pointer > p.pointer && p'.commands[p'.pointer-1]== ']' && valid_loop(p.commands[p.pointer+1.. p'.pointer-1]));
    assert s == s && p.commands == p'.commands && ((s.memory[s.pointer] > 0) ==> pointer_moved_up(p,p'));
    assert p.commands[p.pointer]=='[';
    assert max_steps(p, s, p', s);
    assert p.pointer < |p.commands|;
    assert max_steps(p, s, p', s);
    assert valid_input(p'.input);
    assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
    // assert p.commands[k]==p.commands[p'.pointer-1];
    // assert p.commands[k]==']';
    // assert p'.pointer > k > p.pointer;
    // assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);

  }

lemma MaxStepsStartLoop(p: Program, s: State)
  requires valid_program(p)
  requires state_reqs(s)
  requires 0 <= p.pointer < |p.commands|
  requires p.commands[p.pointer] == '['
  requires valid_input(p.input)
  ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
    {
      if s.memory[s.pointer] == 0 {
        StartLoopStepHelp(p, s);
      } else if s.memory[s.pointer] > 0{
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert pointer_moved_up(p, p');
        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s) && valid_input(p'.input);
      }
    }

lemma MaxStepsEndLoop(p: Program, s: State)
  requires valid_program(p)
  requires state_reqs(s)
  requires 0 <= p.pointer < |p.commands|
  requires p.commands[p.pointer] == ']'
  requires valid_input(p.input)
  ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
    {
      if s.memory[s.pointer] > 0 {
        assert valid_loop(p.commands);
        assert exists k::  0<= k < p.pointer && p.commands[k]== '[' && valid_loop(p.commands[k+1..p.pointer]);
        var k :|  0<= k < p.pointer && p.commands[k]== '[' && valid_loop(p.commands[k+1..p.pointer]);
        var p' := Program(p.commands, k+1, p.input);
        assert valid_program(p');
        assert s.memory[s.pointer] > 0;
        assert p'.pointer == k+1;
        assert 0 < p'.pointer <= p.pointer;
        assert program_step(s, p, s, p');
        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
      } else if s.memory[s.pointer] == 0{
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert pointer_moved_up(p, p');

        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
      }
    }

lemma MaxStepsMove(p: Program, s: State)
  requires 0 <= p.pointer < |p.commands|
  requires valid_program(p)
  requires state_reqs(s)
  requires p.commands[p.pointer] in ['<', '>']
  requires 0 <= s.pointer < |s.memory|
  requires valid_input(p.input)
  ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') && valid_input(p'.input)
{
  var i := p.pointer+1;
    while i < |p.commands| && p.commands[i] ==p.commands[p.pointer]
    decreases |p.commands|-i
    invariant i <= |p.commands|
    invariant forall j:: p.pointer <= j < i ==> p.commands[j] == p.commands[p.pointer]
    {
        i := i+1;
    }
    var mem := s.memory;
    // var newVal := s.memory[s.pointer];
    // assert enough_input(p);
    /*assert forall j:: p.pointer <= j < i ==> p.commands[j] != ',';
    var s2 := set j| p.pointer <= j < i && p.commands[j]==',';
    assert forall j:: p.pointer <= j < i ==> (!(j in s2));
    var s3 := set j | i <= j < |p.commands| && p.commands[j] == ',';
    var s4 := set j | p.pointer <= j < |p.commands| && p.commands[j]==',';
    assert s4 == s2+s3;
    assert |s4| == |s2|+|s3|;
    // assert forall j :: p.pointer <= j < i ==> !(j in s2);
    assert |s2|==0;*/
    var p' := Program(p.commands, i, p.input);
    // assert enough_input(p');
    // count := count_commands(p, p', ['+', '-']);
    var count := 0;
    if p.commands[p.pointer] == '>'{
      count := p'.pointer-p.pointer;
      // mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+p'.pointer-p.pointer)%256] + mem[s.pointer+1..];
    }else if p.commands[p.pointer]=='<'{
      count := p.pointer-p'.pointer;
      // mem :=   mem[..s.pointer] + [(s.memory[s.pointer]-p'.pointer+p.pointer)%256] + mem[s.pointer+1..];

    }
    
    var point := s.pointer;
    assert 0 <= point;
    if point + count >= |s.memory|{
        point := |s.memory|-1;
    }else if point + count <= 0{
        point := 0;
    }else{
        point := point+count;
    }
    assert point < |s.memory|;
    var s' := StateValue(point, s.memory, s.output);
    assert valid_program(p') && aligned_programs(p, p');
    assert state_reqs(s');
    assert (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == p.commands[p.pointer]));
    assert (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == p.commands[p.pointer])));
    assert (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i]);
    assert max_steps(p, s, p', s');
}

lemma ExistsAdvancedProgram(p: Program)
  requires 0 <= p.pointer < |p.commands|
  ensures exists p': Program :: 
            p'.commands == p.commands &&
            0 <= p.pointer < p'.pointer <= |p.commands|
{
  var p' := Program(p.commands, p.pointer + 1, p.input);
  assert p.pointer + 1 <= |p.commands|;
  assert p'.pointer == p.pointer + 1;
  assert p'.commands == p.commands;
}


lemma ExistsAdvancedIntermediate(ir: IntermediateRep)
  requires 0 <= ir.pointer < |ir.commands|
  ensures exists ir': IntermediateRep :: 
            ir'.commands == ir.commands &&
            0 <= ir.pointer < ir'.pointer <= |ir.commands|
{
  var ir' := IntermediateRep(ir.commands, ir.pointer + 1, ir.input);
  assert ir.pointer + 1 <= |ir.commands|;
  assert ir'.pointer == ir.pointer + 1;
  assert ir'.commands == ir.commands;
}


lemma bigger_step_within_range(p: Program, i: int, k: int, next_command_indices: seq<int>)
requires 0<= i < |p.commands|
requires k== count_consecutive_symbols(p, i)
requires next_command_indices == Changes(p)
requires p.commands[i]=='<' || p.commands[i] == '>'
requires changes_correct(p, next_command_indices)
ensures i in next_command_indices ==> next_step(p, i, k, next_command_indices)
{
  if i in next_command_indices{
    assert p.commands[i] in ['+', '-', '>', '<'];
    assert exists d:: within_length(d, next_command_indices) && next_command_indices[d] == i;
    assert (i+count_consecutive_symbols(p, i) == |p.commands| || (i+count_consecutive_symbols(p, i) < |p.commands| &&i+count_consecutive_symbols(p, i) in next_command_indices));
    assert (i+k== |p.commands| || (i+k< |p.commands| && i+k in next_command_indices));
    assert (inside_the_indices(p, next_command_indices, i+k));
    // assert i in next_command_indices;
    inside_the_indices_sum(p, next_command_indices, i, k);
  }

}



lemma IncreasingArrayDoesntAffectMatching(p: Program, ir: seq<Instr>, bound: int, changes: seq<int>)
requires |ir| == bound+1
requires valid_program(p)
requires changes == Changes(p)
requires 0<= bound < |ir|
requires 0<= bound < |changes|
requires 0<= changes[bound] < |p.commands|
requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
requires matched_forall_loop(p, ir[..bound], changes, bound)
ensures matched_forall_loop(p, ir, changes, bound)
{
  forall l| 0<= l < bound
  ensures matched_command_with_ir(p, ir, l, changes)
  {
    assert ir[..bound][l] == ir[l];
    assert matched_command_with_ir(p, ir[..bound], l, changes);
    assert (match ir[l]
    case Inc(k) => (
          ((k>= 0 ==> ((p.commands[changes[l]]=='+') && k==count_consecutive_symbols(p, changes[l]))) && (k<0 ==> (p.commands[changes[l]]=='-')&&(-k)==count_consecutive_symbols(p, changes[l])))
    )
    case Move(k) => 
          ((k>= 0 ==> ((p.commands[changes[l]]=='>') && k==count_consecutive_symbols(p, changes[l]))) && (k<0 ==> (p.commands[changes[l]]=='<')&&(-k)==count_consecutive_symbols(p, changes[l])))
    case UserInput => p.commands[changes[l]] == ','
    case Print => p.commands[changes[l]] == '.'
    case Jump(dest, direction) => ((p.commands[changes[l]] == ']' && direction == false) || (p.commands[changes[l]] == '[' && direction == true))
    );
    assert matched_command_with_ir(p, ir, l, changes);
  }
}
predicate strictly_increasing(s: seq<int>)
requires |s| > 0
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] 
}
lemma LemmaStrictlyIncreasing(s: seq<int>)
  requires |s| > 0
  requires forall i :: 1 <= i < |s| ==> s[i - 1] < s[i] 
  ensures strictly_increasing(s)
{
  
  forall i, j | 0 <= i < j < |s| 
    ensures s[i] < s[j]
  {
    if j == i + 1 {
      assert s[i] < s[j];
    } else {
      assert i < j - 1;
      assert j - 1 < j;
      LemmaStrictlyIncreasing(s[..j]);
      assert s[i] < s[j-1]; 
      assert s[j-1] < s[j];
      assert s[i] < s[j];
    }
  }
}



}