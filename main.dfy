include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"
include "triviallemmas.dfy"
include "loops.dfy"



module BrainFun {
import opened Lemmas
import opened Common
import opened Steps
import opened Equivalence
import opened Trivial
import opened Loops

method CreateFinalIR(p: Program, commands: seq<Instr>) returns (result: IntermediateRep)
requires valid_program(p) //Trivially proven
requires valid_input(p.input) //Trivially proven
requires |commands| == |Changes(p)| //Not trivially proven
requires changes_correct(p, Changes(p)) //Already proven
requires matched_forall_loop(p, commands, Changes(p), |commands|) //Not trivially proven yet
ensures valid_ir(result)
ensures aligned_instructions(p, result)
ensures valid_input(result.input)
ensures EquivalentReps(p, InitialState(), result)

{
  result := IntermediateRep(commands, 0, p.input);
    var s:= InitialState();
  // assert aligned_instructions(p, compiled_ir);
  //TODO: remove the assumption here and replace with a pre-cond
  assume valid_ir(result);
  MaxSteps(p, InitialState());
  IrStep(result, InitialState());
  AlignmentMeansEquivalence(p, InitialState(), result);
  assert valid_input(result.input);
  assert EquivalentReps(p, InitialState(), result);

}

method AddElementToStack(loop: seq<int>, commands: seq<Instr>) returns (result: seq<int>)
requires loop_less_than_commands(loop, commands)
requires |commands| > 0
ensures loop_less_than_commands(result, commands)

{
  result := loop;
  assert loop_less_than_commands(result, commands);
  result := result + [|commands|-1];
  assert loop_less_than_commands(result, commands);
}


//TODO: make sure that all of these hold before calling from main function, especially need to fix the commands[index] one :)
method ReplaceElementInInstr(p: Program, commands: seq<Instr>, index: int, indices: seq<int>, j: int) returns (result: seq<Instr>)
requires 0 <= index < |commands|
requires valid_program(p)
requires indices == Changes(p)
requires changes_correct(p, indices)
requires 0 <= j <= |indices|
requires 0 <= j <= |commands|
requires commands[index] == Jump(0, true)
requires matched_forall_loop(p, commands, indices, j)
ensures |result| == |commands|
ensures matched_forall_loop(p, result, indices, j)
{
  result := commands[..index] + [Jump(|commands|-1, true)] + commands[index+1..];
  ReplacingJumpWithJump(p, commands, result, index, indices, j);
}


// The main compile method, still need to verify that the result is correct :D
method Compile(p: Program)  returns (result: IntermediateRep)
  requires valid_program(p)
  requires |p.commands| > 0
  // requires |p.input| > 0
  requires |p.input| == |p.commands|
  requires p.pointer == 0
  requires valid_input(p.input)
  
  ensures valid_ir(result)
  ensures valid_input(result.input)
  ensures EquivalentReps(p, InitialState(), result)

{
  var i: int := 0;
  var j: int := 0;

  var loop_start_stack: seq<int> := []; 
  var next_command_indices := Changes(p);
  ChangeLemma(p, next_command_indices);
  ForAllHelper(p, next_command_indices);
  assert changes_correct(p, next_command_indices);
  assert forall d:: 0 <= d < |next_command_indices| ==> 0<= next_command_indices[d] < |p.commands|;
  assert sub_changes(p, next_command_indices);
  assert sub_changes_1_step(p, next_command_indices);
  ForAllStep(p, next_command_indices);
  ForAllStep2(p, next_command_indices);
  assert sub_changes_inclusion(p, next_command_indices);
  assert sub_changes_inclusion_1_step(p, next_command_indices);
  var indices_of_i: seq<int> := [];
  assert i in next_command_indices;
  assert sub_changes_inclusion(p, next_command_indices);
  assert sub_changes_inclusion_1_step(p, next_command_indices);
  assert 0 in next_command_indices;
  assert 0 < |p.commands|;
  assert (0 < |p.commands| && 0 in next_command_indices);
  assert i == 0;
  assert (i < |p.commands| && i in next_command_indices);
  assert inside_the_indices(p, next_command_indices, i);
  var commands: seq<Instr> := [];
  assert j==0;
  assert next_command_indices[j]==i;
  assert !(j>0);
  interpret_changes_correct(p, next_command_indices);
  assert j>0 ==> matched_command_with_ir(p, commands, j-1, next_command_indices);
  while i < |p.commands|
    invariant i >= 0
    invariant |commands|>=0
    decreases |p.commands| - i
    invariant sub_changes_inclusion_1_step(p, next_command_indices)
    invariant inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    invariant forall k:: k in indices_of_i ==> k < |p.commands| && inside_the_indices(p, next_command_indices, i)
    invariant forall k:: k in indices_of_i ==> i>k && k in next_command_indices
    invariant forall k:: k in indices_of_i ==> k in next_command_indices
    invariant j < |next_command_indices| ==> next_command_indices[j]==i
    invariant i >= |p.commands| ==> !(i in next_command_indices)
    invariant i >= |p.commands| ==> j >= |next_command_indices|
    invariant j <= |next_command_indices| && indices_of_i == next_command_indices[..j]
    invariant !(i in indices_of_i)
    invariant j == |commands|
    invariant j == |indices_of_i|
    invariant matched_forall_loop(p, commands, next_command_indices, j)
    invariant in_bounds_commands(p, next_command_indices)
    invariant loop_less_than_commands(loop_start_stack, commands)
  {
    assert loop_less_than_commands(loop_start_stack, commands);
    assert j == |indices_of_i|;
    assert j <= |next_command_indices| ==> indices_of_i == next_command_indices[..j];
    assert inside_the_indices(p, next_command_indices, i) && i < |p.commands| ==> i in next_command_indices;
    assert i < |p.commands|;
    assert inside_the_indices(p, next_command_indices, i) ==> i in next_command_indices;
    assert j < |next_command_indices| ==> next_command_indices[j]==i;
    var old_i := i;
    assert old_i == i;
    assert j < |next_command_indices| ==> next_command_indices[j]==old_i;
    assert old_i in next_command_indices;
    assert i < |p.commands|;
    AndElim(indices_of_i, i, next_command_indices);
    assert forall k:: k in indices_of_i ==> i> k;// && i!= k;
    assert j == |indices_of_i|;
    indices_of_i := indices_of_i + [i];
    assert indices_of_i[|indices_of_i|-1] == i;
    assert j == |indices_of_i|-1;
    assert indices_of_i[j] == i;
    assert |indices_of_i| == j+1;
    assert j < |next_command_indices| ==> next_command_indices[j]==i;
    assert j <= |next_command_indices| ==> indices_of_i[..j] == next_command_indices[..j];
 
    assert j < |next_command_indices| ==> indices_of_i[j] == next_command_indices[j];
    extension(j, indices_of_i, next_command_indices);
    assert j+1 <= |next_command_indices| ==> indices_of_i == next_command_indices[..j+1];
    assert forall k:: k in indices_of_i ==> k < |p.commands| && inside_the_indices(p, next_command_indices, i);
    assert forall k:: k in indices_of_i ==> k in next_command_indices;
    EquivStatement(indices_of_i, next_command_indices);
    assert forall k:: int_in_seq(k, indices_of_i) ==> int_in_seq(k, next_command_indices);
    assert next_command_indices[j]==i;
    {match p.commands[i]
      case '+' =>
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= count_consecutive_symbols(p, i);
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        assert i in next_command_indices ==> next_step(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        commands := commands+ [Inc(k)]; 
        assert matched_forall_loop(p, commands[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        assert |commands| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        i := temp;
        assert i-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
        assert p.commands[next_command_indices[j]] == '+';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert k >= 0;
        assert commands[j] == Inc(k);
        AndIsImplicationPlus(p, commands, j, next_command_indices, k);
        assert matched_command_with_ir(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, commands);
      case '-' =>
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= count_consecutive_symbols(p, i);
        var neg_k: int := k;
        neg_k := -1*neg_k;
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        assert i in next_command_indices ==> next_step(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        commands := commands+ [Inc(neg_k)];
        assert matched_forall_loop(p, commands[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        assert |commands| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        i := temp;
        assert i-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
        assert p.commands[next_command_indices[j]] == '-';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert neg_k <  0;
        assert commands[j] == Inc(neg_k);
        AndIsImplicationMinus(p, commands, j, next_command_indices, neg_k);
        assert matched_command_with_ir(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, commands);

       case '>' =>
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= count_consecutive_symbols(p, i);
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        bigger_step_within_range(p, i, k, next_command_indices);
        assert i in next_command_indices ==> next_step(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);
        assert p.commands[next_command_indices[j]] == '>';
        commands := commands+ [Move(k)];
        assert matched_forall_loop(p, commands[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        assert |commands| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        i := temp;
        assert i-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
        assert p.commands[next_command_indices[j]] == '>';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert k >= 0;
        assert commands[j] == Move(k);
        AndIsImplicationMoveForwards(p, commands, j, next_command_indices, k);

        assert matched_command_with_ir(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, commands);

      case '<' =>
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= count_consecutive_symbols(p, i);
        var neg_k: int := k;
        neg_k := -1*neg_k;
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        bigger_step_within_range(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        commands := commands+ [Move(neg_k)];
        assert matched_forall_loop(p, commands[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        assert |commands| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        i := temp;
        assert i-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
        assert p.commands[next_command_indices[j]] == '<';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert neg_k <  0;
        assert commands[j] == Move(neg_k);
        AndIsImplicationMoveBackwards(p, commands, j, next_command_indices, neg_k);
        assert matched_command_with_ir(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, commands);

      case '.' | ',' =>        
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= 1;
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        single_step_within_range(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        if p.commands[next_command_indices[j]]== '.'{
          commands := commands+ [Print];
          assert |commands| >0;
          assert matched_forall_loop(p, commands[..j], next_command_indices, j);
          IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
          assert matched_forall_loop(p, commands, next_command_indices, j);
          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert relation_between_old_new(p, old_i, i+k, next_command_indices);

          var temp := i+k;      
          addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
          assert relation_between_old_new(p, old_i, temp, next_command_indices);
          i := temp;
          assert i-old_i == k;
          single_step_within_range(p, old_i, k, next_command_indices);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
          simple_exclusion(p.commands[next_command_indices[j]]);
          assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
          assert commands[j] == Print;
          AndIsImplicationPrint(p, commands, j, next_command_indices);

          
        } else{
          assert p.commands[next_command_indices[j]] == ',';
          commands := commands+ [UserInput];
          assert |commands| >0;

          assert matched_forall_loop(p, commands[..j], next_command_indices, j);
          IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
          assert matched_forall_loop(p, commands, next_command_indices, j);
          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert relation_between_old_new(p, old_i, i+k, next_command_indices);

          var temp := i+k;      
          addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
          assert relation_between_old_new(p, old_i, temp, next_command_indices);
          i := temp;
          assert i-old_i == k;
          single_step_within_range(p, old_i, k, next_command_indices);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
          assert p.commands[next_command_indices[j]] == ',';
          simple_exclusion_2(p.commands[next_command_indices[j]]);
          assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
          assert commands[j] == UserInput;
          AndIsImplicationInput(p, commands, j, next_command_indices);


          
        }
  
        assert matched_command_with_ir(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, commands);

    case '[' | ']' =>
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= 1;
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        single_step_within_range(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);
        assert |commands| >= 0;
        if p.commands[next_command_indices[j]] == '['{

          assert p.commands[next_command_indices[j]] == '[';
          commands := commands+ [Jump(0, true)];
          assert |commands| >0;

          assert matched_forall_loop(p, commands[..j], next_command_indices, j);
          IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
          assert matched_forall_loop(p, commands, next_command_indices, j);
          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert relation_between_old_new(p, old_i, i+k, next_command_indices);

          var temp := i+k;      
          addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
          assert relation_between_old_new(p, old_i, temp, next_command_indices);
          i := temp;
          assert i-old_i == k;
          single_step_within_range(p, old_i, k, next_command_indices);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
          assert p.commands[next_command_indices[j]] == '[';
          simple_exclusion_2(p.commands[next_command_indices[j]]);
          assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
          assert commands[j] == Jump(0, true);
          AndIsImplicationJumpFor(p, commands, j, next_command_indices, 0);
          // assert |commands| >0;
          assert loop_less_than_commands(loop_start_stack, commands);
          loop_start_stack := AddElementToStack(loop_start_stack, commands);
          // assert loop_less_than_commands(loop_start_stack[..|loop_start_stack|-1], commands);
          // SubArrayLoopSubArray(loop_start_stack, commands);
          assert loop_less_than_commands(loop_start_stack, commands);
        } else{
          
          assert p.commands[next_command_indices[j]] == ']';
          commands := commands+ [Jump(0, false)];
          assert |commands| >0;

          assert matched_forall_loop(p, commands[..j], next_command_indices, j);
          IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
          assert matched_forall_loop(p, commands, next_command_indices, j);
          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert relation_between_old_new(p, old_i, i+k, next_command_indices);

          var temp := i+k;      
          addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
          assert relation_between_old_new(p, old_i, temp, next_command_indices);
          i := temp;
          assert i-old_i == k;
          single_step_within_range(p, old_i, k, next_command_indices);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);
          assert p.commands[next_command_indices[j]] == ']';
          simple_exclusion(p.commands[next_command_indices[j]]);
          assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
          assert commands[j] == Jump(0, false);
          AndIsImplicationJumpBack(p, commands, j, next_command_indices, 0);
          if |loop_start_stack| > 0{
            assert loop_less_than_commands(loop_start_stack, commands);
            var start_index := loop_start_stack[|loop_start_stack| - 1];        
            assert start_index in loop_start_stack;
            assert 0 <= start_index < |commands|;
            loop_start_stack := loop_start_stack[0 .. |loop_start_stack| - 1];
            assert |commands[0..start_index]| == start_index;  
            var new_commands := ReplaceElementInInstr(p, commands, start_index, next_command_indices, j+1);
            // var new_commands := commands[0 .. start_index] + [Jump(|commands|-1, true)] + commands[start_index+1..];
            // ReplacingJumpProperties(commands, new_commands, start_index, commands);
            // assert |new_commands| == |commands|;
            assume false;
            ReplacingJumpWithJump(p, commands, new_commands, start_index, next_command_indices, j+1);
          }


        }

        assert matched_command_with_ir(p, commands, j, next_command_indices);
        assert matched_forall_loop(p, commands, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, commands);

    // case ']' =>{ 
    //   // assert ret >= 0;

    //   var k:= 1;
    //   implication_with_and(p, i, k, next_command_indices); 
    //   assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
    //   single_step_within_range_close_loop(p, i, k, next_command_indices);
    //   step_is_indices(p, i, k, next_command_indices);
    //   assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
    //   commands := commands + [Jump(0, false)];
    //   assert |commands|>0;
    //   assert matched_forall_loop(p, commands[..j], next_command_indices, j);
    //   IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
    //   assert matched_forall_loop(p, commands, next_command_indices, j);
    //   assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
    //   assert relation_between_old_new(p, old_i, i+k, next_command_indices);

    //   var temp := i+k;      
    //   addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
    //   assert relation_between_old_new(p, old_i, temp, next_command_indices);
    //   i := temp;
    //   assert i-old_i == k;
    //   single_step_within_range_close_loop(p, old_i, k, next_command_indices);

    //   assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);

    //   assert p.commands[next_command_indices[j]] == ']';
    //   simple_exclusion(p.commands[next_command_indices[j]]);
    //   assert commands[j] == Jump(0, false);
    //   AndIsImplicationJumpBack(p, commands, j, next_command_indices, 0);

    //   assert matched_command_with_ir(p, commands, j, next_command_indices);
    //   assert matched_forall_loop(p, commands, next_command_indices, j+1);
    //   assert in_bounds_commands(p, next_command_indices);
    //   // if |loop_start_stack| > 0{
    //   //   var start_index := loop_start_stack[|loop_start_stack| - 1];        
    //   //   // loop_start_stack := loop_start_stack[0 .. |loop_start_stack| - 1];
    //   //   // assert 0 <= start_index < |commands|;
    //   //   // assert |commands[0..start_index]| == start_index;  
    //   //   // var new_commands := commands[0 .. start_index] + [Jump(|commands|-1, true)] + commands[start_index+1..];
    //   //   // assert |new_commands| == |commands|;
    //   //   // ReplacingJumpWithJump(p, commands, new_commands, start_index, next_command_indices, j+1);

    //   // }

        

    //     // commands := new_commands;


    //     // assert matched_forall_loop(p, commands, next_command_indices, j);
    //     // var k:= 1;
    //     // implication_with_and(p, i, k, next_command_indices); 
    //     // assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
    //     // single_step_within_range(p, i, k, next_command_indices);
    //     // step_is_indices(p, i, k, next_command_indices);
    //     // assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
    //     // assert matched_forall_loop(p, commands, next_command_indices, j);
    //     // assert |commands| >= 0;
    //     // commands := commands + [Jump(0, false)];
    //     // assert |commands|>0;
    //     // assert matched_forall_loop(p, commands[..j], next_command_indices, j);
    //     // IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
    //     // assert matched_forall_loop(p, commands, next_command_indices, j);

    //     // var temp := i+k;      
    //     // addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
    //     // assert relation_between_old_new(p, old_i, temp, next_command_indices);
    //     // i := temp;
    //     // assert i-old_i == k;
    //     // single_step_within_range(p, old_i, k, next_command_indices);

    //     // assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);

    //     // assert p.commands[next_command_indices[j]] == ']';
    //     // simple_exclusion_2(p.commands[next_command_indices[j]]);
    //     // assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
    //     // assert commands[j] == Jump(0, false);
    //     // AndIsImplicationJumpBack(p, commands, j, next_command_indices, 0);

    //     // assert matched_command_with_ir(p, commands, j, next_command_indices);
    //     // assert matched_forall_loop(p, commands, next_command_indices, j+1);
    //     // assert in_bounds_commands(p, next_command_indices);

      
    //     assert loop_less_than_commands(loop_start_stack, commands);
    // }

    case _ => {assume false;}
    
    /*  case ']' =>
        if |loop_start_stack| > 0 {

          var start_index := loop_start_stack[|loop_start_stack| - 1];
        
          loop_start_stack := loop_start_stack[0 .. |loop_start_stack| - 1];
          assert |commands[0..start_index]| == start_index;
          assert matched_forall_loop(p, commands, next_command_indices, j);
          var k:= 1;
          implication_with_and(p, i, k, next_command_indices); 
          assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
          single_step_within_range(p, i, k, next_command_indices);
          step_is_indices(p, i, k, next_command_indices);
          assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert matched_forall_loop(p, commands, next_command_indices, j);
          assert |commands| >= 0;
          commands := commands[0 .. start_index] + [Jump(|commands|, true)] + commands[start_index+1..] + [Jump(start_index,false)];
          assert |commands|>0;
          assert matched_forall_loop(p, commands[..j], next_command_indices, j);
          IncreasingArrayDoesntAffectMatching(p, commands, j, next_command_indices);
          assert matched_forall_loop(p, commands, next_command_indices, j);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert relation_between_old_new(p, old_i, i+k, next_command_indices);

          var temp := i+k;      
          addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
          assert relation_between_old_new(p, old_i, temp, next_command_indices);
          i := temp;
          assert i-old_i == k;
          single_step_within_range(p, old_i, k, next_command_indices);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i);

          assert p.commands[next_command_indices[j]] == '[';
          simple_exclusion_2(p.commands[next_command_indices[j]]);
          assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
          assert commands[j] == Jump(0, true);
          AndIsImplicationJumpBack(p, commands, j, next_command_indices, 0);

          assert matched_command_with_ir(p, commands, j, next_command_indices);
          assert matched_forall_loop(p, commands, next_command_indices, j+1);
          assert in_bounds_commands(p, next_command_indices);

          // assert (|loop_start_stack|>0) ==> loop_start_stack[|loop_start_stack|-1] < start_index;
          // assert (|loop_start_stack|>0) ==> loop_start_stack[|loop_start_stack|-1] <start_index < |commands|;  
          // assert (|loop_start_stack| > 0) ==> loop_start_stack[|loop_start_stack| - 1] < |commands|;
          // assert forall i :: 1 <= i < |loop_start_stack| ==> loop_start_stack[i - 1] < loop_start_stack[i] ;
          // if (|loop_start_stack| > 0) {
          //     LemmaStrictlyIncreasing(loop_start_stack);
          //     AllLessThanLast(loop_start_stack); 
          //     assert forall i :: 0 <= i < |loop_start_stack| ==> loop_start_stack[i] <= loop_start_stack[|loop_start_stack|-1];
          // } else{
          //     assert forall i :: 0 <= i < |loop_start_stack|==> loop_start_stack[i] < loop_start_stack[|loop_start_stack|-1]; 
          // }


          // assert |loop_start_stack| > 0 ==> 0 < loop_start_stack[|loop_start_stack|-1]+1;


        assert |commands|>0;
        } */
    
    }
    assert loop_less_than_commands(loop_start_stack, commands);
    assert j== |commands|-1;
    assert matched_forall_loop(p, commands, next_command_indices, j+1);
    assert in_bounds_commands(p, next_command_indices);

    assert old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, i);
    assert inside_the_indices(p, next_command_indices, i);
    assert j < |next_command_indices| ==> indices_of_i[j] == next_command_indices[j];
    assert j+1 <= |next_command_indices| ==> j < |next_command_indices|;
    assert 1<= j+1 <= |next_command_indices| ==> indices_of_i[j] == next_command_indices[j];
    assert j+1 <= |next_command_indices| ==> indices_of_i == next_command_indices[..j+1];

    var k := j+1;


    addition_preserving_2(indices_of_i, next_command_indices, j, k);

    assert k >= 1;
    assert 1<= k <= |next_command_indices| ==> indices_of_i[k-1] == next_command_indices[k-1];
    addition_preserving_3(indices_of_i, next_command_indices, j, k);
    assert k <= |next_command_indices| ==> indices_of_i == next_command_indices[..k];

    // assert k <= |next_command_indices| ==> indices_of_i == next_command_indices[..k];
    assert matched_forall_loop(p, commands, next_command_indices, k);

    j := k;
    // assert matched_forall_loop(p, commands, next_command_indices, j);


    assert j <= |next_command_indices| ==> indices_of_i == next_command_indices[..j];
    assert 1<= j <= |next_command_indices| ==> indices_of_i[j-1] == next_command_indices[j-1];

    assert j == |commands|;
    assert |commands|-1 == j-1;
    assert j > 0;
    assert matched_forall_loop(p, commands, next_command_indices, j);


    assert i >= 0;
    assert |commands| >=0;
    assert sub_changes_inclusion_1_step(p, next_command_indices);
    assert inside_the_indices(p, next_command_indices, i);
    assert forall k:: k in indices_of_i ==> k < |p.commands| && inside_the_indices(p, next_command_indices, i);
    assert forall k:: k in indices_of_i ==> i>k && k in next_command_indices;
    greater_not_equal(indices_of_i, i);
    assert !(i in indices_of_i);

    assert j==|commands|;
    assert j == |indices_of_i|;
    assert j < |next_command_indices| ==> next_command_indices[j]==i;
    assert in_bounds_commands(p, next_command_indices); 
    in_bounds_commands_implies_not_in(p, next_command_indices, i);
    // interpret_changes_correct(p, next_command_indices, i);
    // assert i >= |p.commands| ==> !(i in next_command_indices);

/*    
    invariant forall k:: k in indices_of_i ==> k in next_command_indices
    invariant i >= |p.commands| ==> !(i in next_command_indices)
    invariant i >= |p.commands| ==> j >= |next_command_indices|
    invariant j <= |next_command_indices| && indices_of_i == next_command_indices[..j]
    invariant !(i in indices_of_i)
*/

  }
  // assert j <= |next_command_indices| && indices_of_i == next_command_indices[..j];
  // assert j == |indices_of_i|;
  // // assert i == |p.commands|;
  // assert j >= |next_command_indices|;

  length_constraints(j, indices_of_i, next_command_indices);
  assert |indices_of_i| == |commands|;
  assert |commands| == |next_command_indices|;
  // assert forall i:: 0<=i<|commands| ==> 0<=Changes(p)[i] < |p.commands|;
  result := CreateFinalIR(p, commands);
  return result;
}

  method Main()
    ensures true  
  {
    print "Hello, World!\n";
  }

}