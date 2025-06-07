include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"

module Trivial{
    import opened Common 
    import opened Steps
    import opened Equivalence

    lemma IndexedImpliesMembership(s: seq<int>)
        ensures forall d :: 0 <= d < |s| ==> s[d] in s
    {}

    lemma EqualIndex(p: seq<char>, k: int, i: int)
        requires 0<= k < |p|
        requires i-1 == k
        ensures p[i-1]==p[k]
    {}

    lemma EqualityPreservedUnderBasicAddition(res: seq<int>, d: int, k: int, p: Program, temp: seq<int>)
        requires |res| > 0
        requires temp == res[1..]
        requires res[0] + k == |p.commands| || res[0]+k in temp
        requires d in res
        requires 0 <= d < |p.commands|
        requires k == count_consecutive_symbols(p, d)
        requires d== res[0]
        ensures  ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res)
        {}
        
    lemma AndIsImplicationMoveBackwards(p: Program, ir: seq<Instr>, index: int, changes: seq<int>, k: int)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
        requires p.commands[changes[index]] == '<'
        requires k == -1*count_consecutive_symbols(p, changes[index])
        requires matched_forall_loop(p, ir, changes, index)
        requires k < 0
        requires ir[index] == Move(k)
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}

    lemma AndIsImplicationJumpFor(p: Program, ir: seq<Instr>, index: int, changes: seq<int>, dest: int)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires changes_correct(p, changes)
        requires p.commands[changes[index]] == '['
        requires matched_forall_loop(p, ir, changes, index)
        requires ir[index] == Jump(dest, true)
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}


    lemma AndIsImplicationJumpBack(p: Program, ir: seq<Instr>, index: int, changes: seq<int>, dest: int)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
        requires p.commands[changes[index]] == ']'
        requires matched_forall_loop(p, ir, changes, index)
        requires ir[index] == Jump(dest, false)
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}

    lemma AndIsImplicationInput(p: Program, ir: seq<Instr>, index: int, changes: seq<int>)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
        requires p.commands[changes[index]] == ','
        requires matched_forall_loop(p, ir, changes, index)
        requires ir[index] == UserInput
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}

    lemma AndIsImplicationPrint(p: Program, ir: seq<Instr>, index: int, changes: seq<int>)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
        requires p.commands[changes[index]] == '.'
        requires matched_forall_loop(p, ir, changes, index)
        requires ir[index] == Print
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}
    lemma subtraction_equiv(p: Program, commands: seq<Instr>, k: int, j: int, next_command_indices: seq<int>)
        requires valid_program(p)
        requires next_command_indices == Changes(p)
        requires 0<= k-1 < |next_command_indices|
        requires 0<= k-1 < |commands|
        requires 0<= next_command_indices[k-1] < |p.commands|
        requires matched_command_with_ir(p, commands, k-1, next_command_indices)
        requires j==k
        ensures matched_command_with_ir(p, commands, j-1, next_command_indices)
    {}

    lemma ForAllStep2(p: Program, res: seq<int>)
      requires changes_correct(p, res)
      requires forall d:: 0 <= d < |res| ==> 0<= res[d] < |p.commands|
      requires sub_changes(p, res)
      ensures forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> next_step(p, d, count_consecutive_symbols(p, d), res)
    {}

    lemma AllLessThanLast(s: seq<int>)
    requires |s| > 0 // Ensure the sequence is not empty
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] // Strictly increasing
    ensures forall i :: 0 <= i < |s| ==> s[i] <= s[|s| - 1] // All elements (except the last) are less than the last
    {}

    lemma AndElim(s: seq<int>, i: int, t: seq<int>)
        requires forall k:: k in s ==> i> k && k in t
        ensures forall k:: k in s ==> i > k
    {}

    lemma EquivStatement(s: seq<int>, s2: seq<int>)
        requires forall k:: k in s ==> k in s2
        ensures forall k:: int_in_seq(k, s) ==> int_in_seq(k, s2)
    {} 

    lemma AndIsImplicationPlus(p: Program, ir: seq<Instr>, index: int, changes: seq<int>, k: int)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
        requires ir[index] == Inc(k)
        requires p.commands[changes[index]] == '+'
        requires k == count_consecutive_symbols(p, changes[index])
        requires k >= 0
        requires ir[index] == Inc(k)
        requires matched_forall_loop(p, ir, changes, index)
        requires ir[index] == Inc(k)
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}

    lemma IncreasingArrayKeepsValid(ir: seq<Instr>)
    requires |ir| >= 1
    requires valid_ir_commands(ir[..|ir|-1])
    requires match ir[|ir|-1]
    case Inc(_) => true
    case _ => false
    ensures valid_ir_commands(ir)
    {}

    lemma IncreasingArrayKeepsValidMove(ir: seq<Instr>)
    requires |ir| >= 1
    requires valid_ir_commands(ir[..|ir|-1])
    requires match ir[|ir|-1]
    case Move(_) => true
    case _ => false
    ensures valid_ir_commands(ir)
    {}

    lemma IncreasingArrayKeepsValidIO(ir: seq<Instr>)
    requires |ir| >= 1
    requires valid_ir_commands(ir[..|ir|-1])
    requires ir[|ir|-1] == Print || ir[|ir|-1] == UserInput
    ensures valid_ir_commands(ir)
    {}

    lemma IncreasingArrayKeepsValidJumpOne(ir: seq<Instr>)
    requires |ir| >= 1
    requires valid_ir_commands(ir[..|ir|-1])
    requires ir[|ir|-1] == Jump(0, true)
    ensures valid_ir_commands(ir)
    {}



    lemma MatchedForallImpliesMatchedOne(p: Program, commands: seq<Instr>, indices: seq<int>, j: int)
    requires valid_program(p)
    requires 0 <= j 
    requires 0 <= j+1 <= |indices|
    requires 0 <= j+1 <= |commands|
    requires indices == Changes(p)
    requires changes_correct(p, indices)
    requires matched_forall_loop(p, commands, indices, j+1)
    ensures matched_command_with_ir(p, commands, j, indices)
    {}

    lemma IncreasingArrayKeepsValidJumpTwo(ir: seq<Instr>)
    requires |ir| >= 1
    requires valid_ir_commands(ir[..|ir|-1])
    requires ir[|ir|-1] == Jump(0, false)
    ensures valid_ir_commands(ir)
    {}


    lemma AndIsImplicationMinus(p: Program, ir: seq<Instr>, index: int, changes: seq<int>, k: int)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
        requires p.commands[changes[index]] == '-'
        requires k == -1*count_consecutive_symbols(p, changes[index])
        requires matched_forall_loop(p, ir, changes, index)
        requires k < 0
        requires ir[index] == Inc(k)
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}

    lemma AndIsImplicationMoveForwards(p: Program, ir: seq<Instr>, index: int, changes: seq<int>, k: int)
        requires valid_program(p)
        requires changes == Changes(p)
        requires 0<= index < |ir|
        requires 0<= index < |changes|
        requires 0<= changes[index] < |p.commands|
        requires p.commands[changes[index]] == '>'
        requires k == count_consecutive_symbols(p, changes[index])
        requires forall d:: 0<= d < |changes| ==> 0<= changes[d] < |p.commands|
        requires matched_forall_loop(p, ir, changes, index)
        requires k >= 0
        requires ir[index] == Move(k)
        ensures matched_command_with_ir(p, ir, index, changes)
        ensures matched_forall_loop(p, ir, changes, index+1)
    {}

    lemma length_constraints(len: int, s1: seq<int>, s2: seq<int>)
        requires len >= |s2|
        requires len == |s1|
        requires len <= |s2| && s1 == s2[..len]
        ensures |s1| == |s2|
    {}

    lemma CompileHelper(p: Program, commands: seq<Instr>, i: int, k: int, next_command_indices: seq<int>, j: int)
    requires next_command_indices == Changes(p)
    requires valid_program(p)
    requires changes_correct(p, next_command_indices)
    requires k == 1
    requires j == |commands|
    requires |commands| <= |next_command_indices|
    requires 0 <= i < |p.commands|
    requires p.commands[i] == '.' || p.commands[i] == ','
    requires matched_forall_loop(p, commands, next_command_indices, j)
    ensures (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k)
    {
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        single_step_within_range(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);

    }

    lemma single_step_within_range(p: Program, i: int, k: int, next_command_indices: seq<int>)
        requires k==1
        requires next_command_indices == Changes(p)
        requires 0<= i < |p.commands|
        requires p.commands[i]==',' || p.commands[i] == '.' || p.commands[i] == '[' || p.commands[i] == ']' 
        requires changes_correct(p, next_command_indices)
        ensures i in next_command_indices ==> next_step(p, i, k, next_command_indices)
    {}
    lemma single_step_within_range_close_loop(p: Program, i: int, k: int, next_command_indices: seq<int>)
        requires k==1
        requires next_command_indices == Changes(p)
        requires 0<= i < |p.commands|
        requires p.commands[i] == ']'
        requires changes_correct(p, next_command_indices)
        ensures i in next_command_indices ==> next_step(p, i, k, next_command_indices)
    {}


}
