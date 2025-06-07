include "lemmas.dfy"
include "common.dfy"
include "steps.dfy"
include "equivalence.dfy"
include "triviallemmas.dfy"
include "loops.dfy"


module CompilationHelper{
    import opened Lemmas
    import opened Common
    import opened Steps
    import opened Equivalence
    import opened Trivial
    import opened Loops

    method AddElementToStack(loop: seq<int>, commands: seq<Instr>) returns (result: seq<int>)
    requires loop_less_than_commands(loop, commands)
    requires |commands| > 0
    requires commands[|commands|-1] == Jump(0, true)
    ensures loop_less_than_commands(result, commands)

    {
    result := loop;
    assert loop_less_than_commands(result, commands);
    result := result + [|commands|-1];
    assert loop_less_than_commands(result, commands);
    }

    method CompilePlus(p: Program, commands: seq<Instr>, i: int, next_command_indices: seq<int>, j: int, old_i: int, loop_start_stack: seq<int>) 
    returns (result: seq<Instr>, new_index: int)
    requires i >= 0
    requires valid_program(p)
    requires next_command_indices == Changes(p)
    requires |p.commands| > 0
    requires p.pointer == 0
    requires valid_input(p.input)
    requires |commands|>=0
    requires changes_correct(p, next_command_indices)
    requires sub_changes_inclusion_1_step(p, next_command_indices)
    requires inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    requires 0<=j < |next_command_indices|
    requires j < |next_command_indices| ==> next_command_indices[j]==i
    requires i >= |p.commands| ==> !(i in next_command_indices)
    requires i >= |p.commands| ==> j >= |next_command_indices|
    requires j == |commands|
    requires old_i == i
    requires p.commands[next_command_indices[j]] == '+'
    requires matched_forall_loop(p, commands, next_command_indices, j)
    requires in_bounds_commands(p, next_command_indices)
    requires loop_less_than_commands(loop_start_stack, commands)
    requires valid_ir_commands(commands)
    ensures |result| == |commands|+1
    ensures j < |result| && j < |next_command_indices|
    ensures matched_command_with_ir(p, result, j, next_command_indices)
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures j== |result|-1
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, new_index)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures j+1 <= |next_command_indices| ==> j < |next_command_indices|
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures |result| >0
    ensures relation_between_old_new(p, old_i, new_index, next_command_indices)
    ensures new_index >= 0
    ensures inside_the_indices(p, next_command_indices, new_index) //new_index is either greater than |p.commands| or new_index is in the indices
    ensures new_index >= |p.commands| ==> !(new_index in next_command_indices)
    ensures j+1 <= |next_command_indices|
    ensures j+1 == |result|
    ensures j+1 < |next_command_indices| ==> next_command_indices[j+1]==new_index
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures new_index >= 0
    ensures |commands| >=0
    ensures sub_changes_inclusion_1_step(p, next_command_indices)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures new_index > i


    {
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= count_consecutive_symbols(p, i);
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        assert i in next_command_indices ==> next_step(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);
        
        assert valid_ir_commands(commands);
        result := commands+ [Inc(k)]; 

        assert valid_ir_commands(result[..|result|-1]);
        IncreasingArrayKeepsValid(result);
        assert valid_ir_commands(result);

        assert matched_forall_loop(p, result[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j);
        // assume false;

        assert |result| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        // i := temp;
        assert temp-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);
        assert p.commands[next_command_indices[j]] == '+';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert k >= 0;
        assert result[j] == Inc(k);
        AndIsImplicationPlus(p, result, j, next_command_indices, k);
        assert matched_command_with_ir(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, result);
        new_index := temp;
        assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + count_consecutive_symbols(p, next_command_indices[j]);
        assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
        assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;

    }


    method CompileMinus(p: Program, commands: seq<Instr>, i: int, next_command_indices: seq<int>, j: int, old_i: int, loop_start_stack: seq<int>) 
    returns (result: seq<Instr>, new_index: int)
    requires i >= 0
    requires valid_program(p)
    requires next_command_indices == Changes(p)
    requires |p.commands| > 0
    requires p.pointer == 0
    requires valid_input(p.input)
    requires |commands|>=0
    requires changes_correct(p, next_command_indices)
    requires sub_changes_inclusion_1_step(p, next_command_indices)
    requires inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    requires 0<=j < |next_command_indices|
    requires j < |next_command_indices| ==> next_command_indices[j]==i
    requires i >= |p.commands| ==> !(i in next_command_indices)
    requires i >= |p.commands| ==> j >= |next_command_indices|
    requires j == |commands|
    requires old_i == i
    requires p.commands[next_command_indices[j]] == '-'
    requires matched_forall_loop(p, commands, next_command_indices, j)
    requires in_bounds_commands(p, next_command_indices)
    requires loop_less_than_commands(loop_start_stack, commands)
    requires valid_ir_commands(commands)
    ensures |result| == |commands|+1
    ensures j < |result| && j < |next_command_indices|
    ensures matched_command_with_ir(p, result, j, next_command_indices)
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures j== |result|-1
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, new_index)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures j+1 <= |next_command_indices| ==> j < |next_command_indices|
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures |result| >0
    ensures relation_between_old_new(p, old_i, new_index, next_command_indices)
    ensures p.commands[next_command_indices[j]] == '-'
    ensures new_index >= 0
    ensures inside_the_indices(p, next_command_indices, new_index) //new_index is either greater than |p.commands| or new_index is in the indices
    ensures new_index >= |p.commands| ==> !(new_index in next_command_indices)
    ensures j+1 <= |next_command_indices|
    ensures j+1 == |result|
    ensures j+1 < |next_command_indices| ==> next_command_indices[j+1]==new_index
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures new_index >= 0
    ensures |commands| >=0
    ensures sub_changes_inclusion_1_step(p, next_command_indices)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures new_index > i


    {
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

        result := commands+ [Inc(neg_k)];

        assert valid_ir_commands(result[..|result|-1]);
        IncreasingArrayKeepsValid(result);
        assert valid_ir_commands(result);


        assert matched_forall_loop(p, result[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j);

        assert |result| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        assert temp-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);
        assert p.commands[next_command_indices[j]] == '-';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert neg_k <  0;
        assert result[j] == Inc(neg_k);
        AndIsImplicationMinus(p, result, j, next_command_indices, neg_k);
        assert matched_command_with_ir(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, result);
       new_index := temp;
        assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + count_consecutive_symbols(p, next_command_indices[j]);
        assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
        assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;

    }

    method CompileRightShift(p: Program, commands: seq<Instr>, i: int, next_command_indices: seq<int>, j: int, old_i: int, loop_start_stack: seq<int>) 
    returns (result: seq<Instr>, new_index: int)
    requires i >= 0
    requires valid_program(p)
    requires next_command_indices == Changes(p)
    requires |p.commands| > 0
    requires p.pointer == 0
    requires valid_input(p.input)
    requires |commands|>=0
    requires changes_correct(p, next_command_indices)
    requires sub_changes_inclusion_1_step(p, next_command_indices)
    requires inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    requires 0<=j < |next_command_indices|
    requires j < |next_command_indices| ==> next_command_indices[j]==i
    requires i >= |p.commands| ==> !(i in next_command_indices)
    requires i >= |p.commands| ==> j >= |next_command_indices|
    requires j == |commands|
    requires old_i == i
    requires p.commands[next_command_indices[j]] == '>'
    requires matched_forall_loop(p, commands, next_command_indices, j)
    requires in_bounds_commands(p, next_command_indices)
    requires loop_less_than_commands(loop_start_stack, commands)
    requires valid_ir_commands(commands)
    ensures |result| == |commands|+1
    ensures j < |result| && j < |next_command_indices|
    ensures matched_command_with_ir(p, result, j, next_command_indices)
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures j== |result|-1
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, new_index)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures j+1 <= |next_command_indices| ==> j < |next_command_indices|
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures |result| >0
    ensures relation_between_old_new(p, old_i, new_index, next_command_indices)
    ensures p.commands[next_command_indices[j]] == '>'
    ensures new_index >= 0
    ensures inside_the_indices(p, next_command_indices, new_index) //new_index is either greater than |p.commands| or new_index is in the indices
    ensures new_index >= |p.commands| ==> !(new_index in next_command_indices)
    ensures j+1 <= |next_command_indices|
    ensures j+1 == |result|
    ensures j+1 < |next_command_indices| ==> next_command_indices[j+1]==new_index
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures new_index >= 0
    ensures |commands| >=0
    ensures sub_changes_inclusion_1_step(p, next_command_indices)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures new_index > i


    {
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

        assert valid_ir_commands(commands);

        result := commands+ [Move(k)];

        assert valid_ir_commands(result[..|result|-1]);
        IncreasingArrayKeepsValidMove(result);
        assert valid_ir_commands(result);


        assert matched_forall_loop(p, result[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j);

        assert |result| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        assert temp-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);
        assert p.commands[next_command_indices[j]] == '>';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert k >= 0;
        assert result[j] == Move(k);
        AndIsImplicationMoveForwards(p, result, j, next_command_indices, k);

        assert matched_command_with_ir(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, result);
      new_index := temp;
        assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + count_consecutive_symbols(p, next_command_indices[j]);
        assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
        assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;

    }

    method CompileLeftShift(p: Program, commands: seq<Instr>, i: int, next_command_indices: seq<int>, j: int, old_i: int, loop_start_stack: seq<int>) 
    returns (result: seq<Instr>, new_index: int)
    requires i >= 0
    requires valid_program(p)
    requires next_command_indices == Changes(p)
    requires |p.commands| > 0
    requires p.pointer == 0
    requires valid_input(p.input)
    requires |commands|>=0
    requires changes_correct(p, next_command_indices)
    requires sub_changes_inclusion_1_step(p, next_command_indices)
    requires inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    requires 0<=j < |next_command_indices|
    requires j < |next_command_indices| ==> next_command_indices[j]==i
    requires i >= |p.commands| ==> !(i in next_command_indices)
    requires i >= |p.commands| ==> j >= |next_command_indices|
    requires j == |commands|
    requires old_i == i
    requires p.commands[next_command_indices[j]] == '<'
    requires matched_forall_loop(p, commands, next_command_indices, j)
    requires in_bounds_commands(p, next_command_indices)
    requires loop_less_than_commands(loop_start_stack, commands)
    requires valid_ir_commands(commands)
    ensures |result| == |commands|+1
    ensures j < |result| && j < |next_command_indices|
    ensures matched_command_with_ir(p, result, j, next_command_indices)
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures j== |result|-1
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, new_index)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures j+1 <= |next_command_indices| ==> j < |next_command_indices|
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures |result| >0
    ensures relation_between_old_new(p, old_i, new_index, next_command_indices)
    ensures p.commands[next_command_indices[j]] == '<'
    ensures new_index >= 0
    ensures inside_the_indices(p, next_command_indices, new_index) //new_index is either greater than |p.commands| or new_index is in the indices
    ensures new_index >= |p.commands| ==> !(new_index in next_command_indices)
    ensures j+1 <= |next_command_indices|
    ensures j+1 == |result|
    ensures j+1 < |next_command_indices| ==> next_command_indices[j+1]==new_index
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures new_index >= 0
    ensures |commands| >=0
    ensures sub_changes_inclusion_1_step(p, next_command_indices)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures new_index > i


    {
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

        assert valid_ir_commands(commands);
        
        result := commands+ [Move(neg_k)];

        assert valid_ir_commands(result[..|result|-1]);
        IncreasingArrayKeepsValidMove(result);
        assert valid_ir_commands(result);

        assert matched_forall_loop(p, result[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j);

        assert |result| >0;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);

        assert temp-old_i == k;
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);
        assert p.commands[next_command_indices[j]] == '<';
        assert k == count_consecutive_symbols(p, next_command_indices[j]);
        assert neg_k <  0;
        assert result[j] == Move(neg_k);
        AndIsImplicationMoveBackwards(p, result, j, next_command_indices, neg_k);
        assert matched_command_with_ir(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, result);
        new_index := temp;
        assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + count_consecutive_symbols(p, next_command_indices[j]);
        assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
        assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;

    }
    method CompileTrueJump(p: Program, commands: seq<Instr>, i: int, next_command_indices: seq<int>, j: int, old_i: int, loop_start_stack: seq<int>) 
    returns (result: seq<Instr>, new_index: int)
    requires i >= 0
    requires valid_program(p)
    requires next_command_indices == Changes(p)
    requires |p.commands| > 0
    requires p.pointer == 0
    requires valid_input(p.input)
    requires |commands|>=0
    requires changes_correct(p, next_command_indices)
    requires sub_changes_inclusion_1_step(p, next_command_indices)
    requires inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    requires 0<=j < |next_command_indices|
    requires j < |next_command_indices| ==> next_command_indices[j]==i
    requires i >= |p.commands| ==> !(i in next_command_indices)
    requires i >= |p.commands| ==> j >= |next_command_indices|
    requires j == |commands|
    requires old_i == i
    requires p.commands[next_command_indices[j]] == '['
    requires matched_forall_loop(p, commands, next_command_indices, j)
    requires in_bounds_commands(p, next_command_indices)
    requires loop_less_than_commands(loop_start_stack, commands)
    requires valid_ir_commands(commands)
    ensures |result| == |commands|+1
    ensures j < |result| && j < |next_command_indices|
    ensures matched_command_with_ir(p, result, j, next_command_indices)
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures j== |result|-1
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, new_index)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures j+1 <= |next_command_indices| ==> j < |next_command_indices|
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures |result| >0
    ensures relation_between_old_new(p, old_i, new_index, next_command_indices)
    ensures p.commands[next_command_indices[j]] == '['
    ensures new_index >= 0
    ensures inside_the_indices(p, next_command_indices, new_index) //new_index is either greater than |p.commands| or new_index is in the indices
    ensures new_index >= |p.commands| ==> !(new_index in next_command_indices)
    ensures j+1 <= |next_command_indices|
    ensures j+1 == |result|
    ensures j+1 < |next_command_indices| ==> next_command_indices[j+1]==new_index
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures new_index >= 0
    ensures |commands| >=0
    ensures sub_changes_inclusion_1_step(p, next_command_indices)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures new_index > i
    ensures result[|result|-1] == Jump(0, true)


    {
        var k := 1;
        assert p.commands[next_command_indices[j]] == '[';
        assert j == |commands|;
        assert valid_ir_commands(commands);
        result := commands+ [Jump(0, true)];


        assert result[|result|-1] == Jump(0, true);
        assert valid_ir_commands(result[..|result|-1]);
        IncreasingArrayKeepsValidJumpOne(result);
        assert valid_ir_commands(result);
        assert j == |result|-1;
        assert result[j] == Jump(0, true);
        assert |result| >0;
        assert matched_forall_loop(p, result[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j);
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);

        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);
        assert temp-old_i == k;
        single_step_within_range(p, old_i, k, next_command_indices);

        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);

        assert p.commands[next_command_indices[j]] == '[';
        simple_exclusion_2(p.commands[next_command_indices[j]]);
        assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
        assert result[j] == Jump(0, true);
        assert result[|result|-1] == Jump(0, true);
        assert 0<= j < |result|;
        assert 0<= j < |next_command_indices|;
        assert 0<= next_command_indices[j] < |p.commands|;
        // assume matched_forall_loop(p, result, next_command_indices, j);
        AndIsImplicationJumpFor(p, result, j, next_command_indices, 0);
        assert matched_forall_loop(p, result, next_command_indices, j+1);
        new_index := temp;
        assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + 1;
        assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
        assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;

    }


    method CompileFalseJump(p: Program, commands: seq<Instr>, i: int, next_command_indices: seq<int>, j: int, old_i: int, loop_start_stack: seq<int>) 
    returns (result: seq<Instr>, new_index: int)
    requires i >= 0
    requires valid_program(p)
    requires next_command_indices == Changes(p)
    requires |p.commands| > 0
    requires p.pointer == 0
    requires valid_input(p.input)
    requires |commands|>=0
    requires changes_correct(p, next_command_indices)
    requires sub_changes_inclusion_1_step(p, next_command_indices)
    requires inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    requires 0<=j < |next_command_indices|
    requires j < |next_command_indices| ==> next_command_indices[j]==i
    requires i >= |p.commands| ==> !(i in next_command_indices)
    requires i >= |p.commands| ==> j >= |next_command_indices|
    requires j == |commands|
    requires old_i == i
    requires p.commands[next_command_indices[j]] == ']'
    requires matched_forall_loop(p, commands, next_command_indices, j)
    requires in_bounds_commands(p, next_command_indices)
    requires loop_less_than_commands(loop_start_stack, commands)
    requires valid_ir_commands(commands)
    ensures |result| == |commands|+1
    ensures j < |result| && j < |next_command_indices|
    ensures matched_command_with_ir(p, result, j, next_command_indices)
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures j== |result|-1
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, new_index)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures j+1 <= |next_command_indices| ==> j < |next_command_indices|
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures |result| >0
    ensures relation_between_old_new(p, old_i, new_index, next_command_indices)
    ensures p.commands[next_command_indices[j]] == ']'
    ensures new_index >= 0
    ensures inside_the_indices(p, next_command_indices, new_index) //new_index is either greater than |p.commands| or new_index is in the indices
    ensures new_index >= |p.commands| ==> !(new_index in next_command_indices)
    ensures j+1 <= |next_command_indices|
    ensures j+1 == |result|
    ensures j+1 < |next_command_indices| ==> next_command_indices[j+1]==new_index
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures new_index >= 0
    ensures |commands| >=0
    ensures sub_changes_inclusion_1_step(p, next_command_indices)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures new_index > i
    ensures result[|result|-1] == Jump(0, false)


    {
        var k := 1;
        assert p.commands[next_command_indices[j]] == ']';
        assert j == |commands|;
        assert valid_ir_commands(commands);
        result := commands+ [Jump(0, false)];


        assert result[|result|-1] == Jump(0, false);
        assert valid_ir_commands(result[..|result|-1]);
        IncreasingArrayKeepsValidJumpTwo(result);
        assert valid_ir_commands(result);
        assert j == |result|-1;
        assert result[j] == Jump(0, false);
        assert |result| >0;
        assert matched_forall_loop(p, result[..j], next_command_indices, j);
        IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j);
        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert relation_between_old_new(p, old_i, i+k, next_command_indices);
        var temp := i+k;      
        addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
        assert relation_between_old_new(p, old_i, temp, next_command_indices);
        assert temp-old_i == k;
        single_step_within_range_close_loop(p, old_i, k, next_command_indices);

        assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);

        assert p.commands[next_command_indices[j]] == ']';
        simple_exclusion(p.commands[next_command_indices[j]]);
        assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
        assert result[j] == Jump(0, false);
        assert result[|result|-1] == Jump(0, false);
        assert 0<= j < |result|;
        assert 0<= j < |next_command_indices|;
        assert 0<= next_command_indices[j] < |p.commands|;
        AndIsImplicationJumpBack(p, result, j, next_command_indices, 0);
        assert matched_forall_loop(p, result, next_command_indices, j+1);
        assert loop_less_than_commands(loop_start_stack, result);
        new_index := temp;
        assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + 1;
        assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
        assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;

    }

    method CompileIO(p: Program, commands: seq<Instr>, i: int, next_command_indices: seq<int>, j: int, old_i: int, loop_start_stack: seq<int>) 
    returns (result: seq<Instr>, new_index: int)
    requires i >= 0
    requires valid_program(p)
    requires next_command_indices == Changes(p)
    requires |p.commands| > 0
    requires p.pointer == 0
    requires valid_input(p.input)
    requires |commands|>=0
    requires changes_correct(p, next_command_indices)
    requires sub_changes_inclusion_1_step(p, next_command_indices)
    requires inside_the_indices(p, next_command_indices, i) //i is either greater than |p.commands| or i is in the indices
    requires 0<=j < |next_command_indices|
    requires j < |next_command_indices| ==> next_command_indices[j]==i
    requires i >= |p.commands| ==> !(i in next_command_indices)
    requires i >= |p.commands| ==> j >= |next_command_indices|
    requires j == |commands|
    requires old_i == i
    requires p.commands[next_command_indices[j]] == ',' || p.commands[next_command_indices[j]] == '.'
    requires matched_forall_loop(p, commands, next_command_indices, j)
    requires in_bounds_commands(p, next_command_indices)
    requires loop_less_than_commands(loop_start_stack, commands)
    requires valid_ir_commands(commands)
    ensures |result| == |commands|+1
    ensures j < |result| && j < |next_command_indices|
    ensures matched_command_with_ir(p, result, j, next_command_indices)
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures j== |result|-1
    ensures matched_forall_loop(p, result, next_command_indices, j+1)
    ensures in_bounds_commands(p, next_command_indices)
    ensures old_i in next_command_indices ==> inside_the_indices(p, next_command_indices, new_index)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures j+1 <= |next_command_indices| ==> j < |next_command_indices|
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures |result| >0
    ensures relation_between_old_new(p, old_i, new_index, next_command_indices)
    ensures p.commands[next_command_indices[j]] == ',' || p.commands[next_command_indices[j]] == '.'
    ensures new_index >= 0
    ensures inside_the_indices(p, next_command_indices, new_index) //new_index is either greater than |p.commands| or new_index is in the indices
    ensures new_index >= |p.commands| ==> !(new_index in next_command_indices)
    ensures j+1 <= |next_command_indices|
    ensures j+1 == |result|
    ensures j+1 < |next_command_indices| ==> next_command_indices[j+1]==new_index
    ensures matched_forall_loop(p, result, next_command_indices, j)
    ensures in_bounds_commands(p, next_command_indices)
    ensures loop_less_than_commands(loop_start_stack, result)
    ensures valid_ir_commands(result)
    ensures new_index >= 0
    ensures |commands| >=0
    ensures sub_changes_inclusion_1_step(p, next_command_indices)
    ensures inside_the_indices(p, next_command_indices, new_index)
    ensures new_index > i


    {
        assert matched_forall_loop(p, commands, next_command_indices, j);
        var k:= 1;
        implication_with_and(p, i, k, next_command_indices); 
        assert (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k);
        single_step_within_range(p, i, k, next_command_indices);
        step_is_indices(p, i, k, next_command_indices);
        assert (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
        assert matched_forall_loop(p, commands, next_command_indices, j);

        if p.commands[next_command_indices[j]]== '.'{
          result := commands+ [Print];
          assert valid_ir_commands(result[..|result|-1]);
          IncreasingArrayKeepsValidIO(result);
          assert valid_ir_commands(result);

          assert |result| >0;
          assert matched_forall_loop(p, result[..j], next_command_indices, j);
          IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
          assert matched_forall_loop(p, result, next_command_indices, j);
          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert relation_between_old_new(p, old_i, i+k, next_command_indices);

          var temp := i+k;      
          addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
          assert relation_between_old_new(p, old_i, temp, next_command_indices);
          assert temp-old_i == k;
          single_step_within_range(p, old_i, k, next_command_indices);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);
          simple_exclusion(p.commands[next_command_indices[j]]);
          assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
          assert result[j] == Print;
          AndIsImplicationPrint(p, result, j, next_command_indices);
          new_index := temp;
          assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + 1;
          assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
          assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;

          
        } else{
          assert p.commands[next_command_indices[j]] == ',';
          result := commands+ [UserInput];
          assert valid_ir_commands(result[..|result|-1]);
          IncreasingArrayKeepsValidIO(result);
          assert valid_ir_commands(result);

          assert |result| >0;

          assert matched_forall_loop(p, result[..j], next_command_indices, j);
          IncreasingArrayDoesntAffectMatching(p, result, j, next_command_indices);
          assert matched_forall_loop(p, result, next_command_indices, j);
          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k);
          assert relation_between_old_new(p, old_i, i+k, next_command_indices);

          var temp := i+k;      
          addition_is_preserving(p, old_i, i, k, temp, next_command_indices);
          assert relation_between_old_new(p, old_i, temp, next_command_indices);
          assert temp-old_i == k;
          single_step_within_range(p, old_i, k, next_command_indices);

          assert (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, temp);
          assert p.commands[next_command_indices[j]] == ',';
          simple_exclusion_2(p.commands[next_command_indices[j]]);
          assert !(p.commands[next_command_indices[j]] in ['+', '-', '<', '>']);
          assert result[j] == UserInput;
          AndIsImplicationInput(p, result, j, next_command_indices);
        new_index := temp;
        assert just_short_length(j, next_command_indices) ==> next_command_indices[j+1] == next_command_indices[j] + 1;
        assert j+1 < |next_command_indices| ==> next_command_indices[j+1] == i + k;
        assert j +1 < |next_command_indices| ==> next_command_indices[j+1] == new_index;


          
        }
  
        assert matched_command_with_ir(p, result, j, next_command_indices);
        assert matched_forall_loop(p, result, next_command_indices, j+1);
        assert in_bounds_commands(p, next_command_indices);
        assert loop_less_than_commands(loop_start_stack, result);
        


    }


}