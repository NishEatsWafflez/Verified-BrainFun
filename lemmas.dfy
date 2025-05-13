include "common.dfy"
include "steps.dfy"
module Lemmas{
    import opened Common
    import opened Steps

lemma ForAllKSteps(p: Program, s: State)
  requires 0 <= p.pointer <= |p.commands|
  requires valid_program(p)
  requires state_reqs(s)
//   requires enough_input(p)
  requires valid_input(p.input)
//   requires enough_input(p)
  requires 0 <= s.pointer < |s.memory|
  requires exists p_next: Program, s_next: State :: 
    (valid_state(s, s_next) && state_reqs(s_next) && 
     aligned_programs(p, p_next) && valid_program(p_next) && 
     max_steps(p, s, p_next, s_next)) && valid_input(p_next.input)
  ensures forall k:: 0<=k ==> (exists p': Program, s': State ::  
    valid_program(p') && state_reqs(s') && 
    program_k_max_steps(p, s, p', s', k)) 
{
    forall k | 0<=k{
        MaxKSteps(p, s, k);
    }
}

lemma IrStep(ir: IntermediateRep, s: State)
    requires state_reqs(s)
    requires valid_input(ir.input)
    requires valid_ir(ir)
    decreases |ir.commands| - ir.pointer; //Need to figure out how to prove decreases or termination as we descend into recursion :0
    // ensures exists ir': IntermediateRep, s': State :: state_reqs(s') && ir_step(ir, s, ir', s')
{
    if ir.pointer == |ir.commands| {
        var ir' := ir;
        var s' := s;
        assert state_reqs(s') && ir_step(ir, s, ir', s');
    }else{
        match ir.commands[ir.pointer]
            case Inc(n) =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var mem := s.memory;
                mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+n)%256] + mem[s.pointer+1..];
                var s' := StateValue(s.pointer, mem, s.output);
                assert state_reqs(s') && ir_step(ir, s, ir', s');
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
                assert state_reqs(s') && ir_step(ir, s, ir', s');
                
            }
            case Print =>{
                var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input);
                assert ir_moved_up(ir, ir');
                var s' := StateValue(s.pointer, s.memory, s.output+ [s.memory[s.pointer] as char]);
                assert state_reqs(s') && ir_step(ir, s, ir', s');
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
                    assert state_reqs(s') && ir_step(ir, s, ir', s');
                } else if |ir.input| > 0{
                    var ir' := IntermediateRep(ir.commands, ir.pointer+1, ir.input[1..]);
                    assert ir_moved_up(ir, ir');
                    var mem := s.memory;
                    mem :=   mem[..s.pointer] + [ir.input[0] as int] + mem[s.pointer+1..];
                    assert mem[s.pointer] == ir.input[0] as int;
                    var s' := StateValue(s.pointer, mem, s.output);
                    assert s'.memory[s.pointer] == ir.input[0] as int;
                    assert state_reqs(s') && ir_step(ir, s, ir', s');   
                }
            }
            case Loop(body) =>{
                // var new_body := IntermediateRep(body.commands, body.pointer, ir.input);
                // IrStep(new_body, s); //Need to define a predicate that assumes recursively all internal structures are valid :D
                assert true;
            }
    }
}
lemma MaxKSteps(p: Program, s: State, k: int) 
  requires 0 <= p.pointer <= |p.commands|
  requires valid_program(p)
  requires state_reqs(s)
//   requires enough_input(p)
  requires valid_input(p.input)
//   requires enough_input(p)
  requires 0 <= k
  requires 0 <= s.pointer < |s.memory|
  requires exists p_next: Program, s_next: State :: 
    (valid_state(s, s_next) && state_reqs(s_next) && 
     aligned_programs(p, p_next) && valid_program(p_next) && 
     max_steps(p, s, p_next, s_next)) && valid_input(p_next.input)
  ensures (exists p': Program, s': State ::  
    valid_program(p') && state_reqs(s') && 
    program_k_max_steps(p, s, p', s', k)) 
decreases k
{
  if k == 0 {
    assert program_k_max_steps(p, s, p, s, 0);
  } else {
    // var i:= 0;
    // while i < k
    // decreases k-i

    
        assert exists p_next, s_next :: 
        (valid_state(s, s_next) && state_reqs(s_next) && 
        aligned_programs(p, p_next) && valid_program(p_next) && 
        max_steps(p, s, p_next, s_next));

        var p': Program, s': State :| valid_state(s, s')&& state_reqs(s') && aligned_programs(p, p')&& valid_program(p') && max_steps(p, s, p', s') && valid_input(p'.input); //&& enough_input(p');
        // i:=i+1;
        assert valid_program(p');
        MaxSteps(p', s');
        MaxKSteps(p', s', k - 1);

    
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
// We want to show that if the CountCommands is equivalent to progressing and adding 1 for every '+' and subtracting 1 for every '-'
lemma CountCommandsLemma(p: Program, p': Program, symbols: seq<char>)
requires |symbols| == 2
requires valid_program(p)
{
    var i:= p.pointer;
    var count := 0;
    while i < |p.commands| && p.commands[i] in ['+', '-']
    decreases |p.commands|-i
    invariant i <= |p.commands|
    invariant forall j:: p.pointer <= j < i ==> p.commands[j] in ['+', '-']
    {
        if p.commands[i] == '+'{
            count := count + 1;
        } else{
            count := count-1;
        }
        i := i+1;
    }
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
    var count := 0;
    if p.commands[p.pointer] == '+'{
        count := 1;
    } else{
        count := -1;
    }
    while i < |p.commands| && p.commands[i] in ['+', '-']
    decreases |p.commands|-i
    invariant i <= |p.commands|
    invariant forall j:: p.pointer <= j < i ==> p.commands[j] in ['+', '-']
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
    count := count_commands(p, p', ['+', '-']);
    mem :=   mem[..s.pointer] + [(s.memory[s.pointer]+count)%256] + mem[s.pointer+1..];
    var s' := StateValue(s.pointer, mem, s.output);
    assert valid_program(p') && aligned_programs(p, p');
    assert state_reqs(s');
    assert (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] in ['+', '-']));
    assert (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] in ['+', '-'])));
    assert (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i]);
    assert count == count_commands(p, p', ['+', '-']);
    assert valid_input(p'.input);
    assert s'.memory[s.pointer] == (s.memory[s.pointer]+count)%256;
    assert (s'.memory[s.pointer] == (s.memory[s.pointer]+count_commands(p, p', ['+', '-']))%256);
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

    requires valid_input(p.input);
    ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
{
    var mem := s.memory;
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
    }else{
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

/*lemma MaxStepsStartLoop(p: Program, s: State)
    requires valid_program(p)
    requires state_reqs(s)
    requires 0 <= p.pointer < |p.commands|-1
    requires p.commands[p.pointer] == '['
    // ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') 
{
    assert balanced_brackets(p);
    if s.memory[s.pointer] > 0{
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
    }else{
        var i := p.pointer+1;
        var count := 0;

        while (i < |p.commands| && (p.commands[i] != ']' || count != 1))
            decreases |p.commands|-i
            invariant i <= |p.commands|
            // invariant count >= 0
        {
            if p.commands[i] == '[' {count := count + 1;}
            else if p.commands[i] == ']' {count := count - 1;}
            i := i+1;
        }
        assert i < |p.commands|;
        var p' := Program(p.commands, i+1, p.input);
    }
}*/

//  lemma MaxStepsStartLoop(p: Program, s: State)
//         requires valid_program(p)
//         requires state_reqs(s)
//         requires 0 <= p.pointer < |p.commands|-1
//         requires p.commands[p.pointer] == '['
//         requires MatchingBracketExists(p.commands, p.pointer)
//         // ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s') 
//     {
//         assert balanced_brackets(p);
//         if s.memory[s.pointer] > 0{
//             var p' := Program(p.commands, p.pointer+1, p.input);
//             assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
//         }else{
//             var index := FindMatchingBracketIndex(p.commands, p.pointer+1)+1;
//             var p' := Program(p.commands, index, p.input);
//             assert 0 <= index <= |p.commands|;
//             assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
//         }
//     }
lemma MaxStepsStartLoop(p: Program, s: State)
        requires valid_program(p)
        requires state_reqs(s)
        requires 0 <= p.pointer < |p.commands|
        requires p.commands[p.pointer] == '['
        requires valid_input(p.input)
        ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
    {
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert pointer_moved_up(p, p');

        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
    }

lemma MaxStepsEndLoop(p: Program, s: State)
        requires valid_program(p)
        requires state_reqs(s)
        requires 0 <= p.pointer < |p.commands|
        requires p.commands[p.pointer] == ']'
        requires valid_input(p.input)
        ensures exists p': Program, s': State :: valid_program(p') && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p') && max_steps(p, s, p', s')  && valid_input(p'.input)
    {
        var p' := Program(p.commands, p.pointer+1, p.input);
        assert pointer_moved_up(p, p');

        assert valid_program(p') && state_reqs(s) && valid_state(s, s) && aligned_programs(p, p') && max_steps(p, s, p', s);
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
    var count := 0;
    if p.commands[p.pointer] == '+'{
        count := 1;
    } else{
        count := -1;
    }
    while i < |p.commands| && p.commands[i] in ['>', '<']
    decreases |p.commands|-i
    invariant i <= |p.commands|
    invariant forall j:: p.pointer <= j < i ==> p.commands[j] in ['>', '<']
    {
        i := i+1;
    }
    var p' := Program(p.commands, i, p.input);
    
    count := count_commands(p, p', ['>', '<']);
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
    assert (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] in ['>', '<']));
    assert (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] in ['>', '<'])));
    assert (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i]);
    assert count == count_commands(p, p', ['>', '<']);
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

lemma LemmaStrictlyIncreasing(s: seq<int>)
  requires |s| > 0
  requires forall i :: 1 <= i < |s| ==> s[i - 1] < s[i] 
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] 
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


lemma AllLessThanLast(s: seq<int>)
  requires |s| > 0 // Ensure the sequence is not empty
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] // Strictly increasing
  ensures forall i :: 0 <= i < |s| ==> s[i] <= s[|s| - 1] // All elements (except the last) are less than the last
{
}

lemma ExistsValidState(s: State)
requires state_reqs(s)
ensures exists s': State:: state_reqs(s')
{
    // exists s': State:: s' == s
}

}