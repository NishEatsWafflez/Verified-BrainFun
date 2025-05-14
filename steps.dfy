include "common.dfy"
module Steps{
    import opened Common

    predicate program_step(s: State, p: Program, s': State, p': Program)
    
    decreases |p.commands|-p.pointer
    requires valid_program(p) && valid_program(p') 
    requires state_reqs(s)
    {
        0 <= p.pointer < |p.commands| && 0 <= p'.pointer < |p'.commands| && p.commands == p'.commands && 
        p.commands != [] ==> //TODO: how to get user input
        match p.commands[p.pointer]
            case '+' => 
                0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory| 
                && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                && ((s.memory[s.pointer] == 255) ==> s'.memory[s.pointer] == 0)
                && (s.memory[s.pointer] != 255 ==> s'.memory[s.pointer] == s.memory[s.pointer]+1) && pointer_moved_up(p, p')
            case '-' => 
                0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory| 
                && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                && ((s.memory[s.pointer] == 0) ==> s'.memory[s.pointer] == 255)
                && (s.memory[s.pointer] != 0 ==> s'.memory[s.pointer] == s.memory[s.pointer]-1) && pointer_moved_up(p, p')
            case '>' => 
                0 <= s.pointer < |s.memory| && s.memory == s'.memory && 0 <= s'.pointer < |s.memory| 
                && ((s.pointer + 1 >= |s.memory|) ==> s'.pointer == |s.memory|-1)
                && ((0 <= s.pointer + 1 < |s.memory|) ==> s'.pointer == s.pointer+1) && pointer_moved_up(p, p')
            case '<' => 
                0 <= s.pointer < |s.memory| && s.memory == s'.memory && 0 <= s'.pointer < |s.memory| 
                && ((s.pointer - 1 < 0) ==> s'.pointer == 0)
                && ((0 <= s.pointer - 1 < |s.memory|) ==> s'.pointer == s.pointer-1) && pointer_moved_up(p, p')
            case '[' => 
                (0 <= s.pointer < |s.memory| && 0 <= s'.pointer < |s.memory| )
                && ((s.memory[s.pointer] > 0) ==> pointer_moved_up(p,p'))
                && (s.memory[s.pointer]== 0 ==> (p'.pointer > p.pointer && p'.commands[p'.pointer-1]== ']' && valid_loop(p.commands[p.pointer+1.. p'.pointer-1])))    //Need to add forall to make sure that at the soonest ]
            case '.' =>
                s.memory == s'.memory && s.pointer == s'.pointer //Add more for printing?
                // && (0 <= s.pointer < |s.memory| && 0 <= s'.pointer < |s.memory| )
                && pointer_moved_up(p, p')
                && s'.output == s.output + [s.memory[s.pointer] as char]
            case ']' => 
                (
                    (0 <= s.pointer < |s.memory| && 0 <= s'.pointer < |s.memory| )
                    && ((s.memory[s.pointer] == 0) ==> pointer_moved_up(p, p'))
                    && (s.memory[s.pointer] > 0 ==> (0 < p'.pointer < p.pointer && p'.commands[p'.pointer-1]== '[' && valid_loop(p.commands[p'.pointer.. p.pointer-1])))
                )
                
                // true
            case ',' =>
                (
                    0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory| 
                    && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                    && (|p.input| > 0 ==> (s'.memory[s.pointer] == p.input[0] as int && p'.input == p.input[1..]))
                    && (|p.input| == 0 ==> (p'.input == p.input && s'.memory[s.pointer]==' ' as int))
                    && pointer_moved_up(p, p')
                )
            case default => false
    }


    predicate ir_step(ir: IntermediateRep, s: State,  ir': IntermediateRep, s': State)
    requires |s.memory| == |s'.memory|
    requires state_reqs(s)
    requires 0 <= ir.pointer 
    requires 0 <= ir'.pointer
    decreases |ir.commands| - ir.pointer //Need to figure out how to prove decreases or termination as we descend into recursion :0
    {
        if ir.pointer == |ir.commands| then ir' == ir && s' == s
        else 
        (ir.pointer < |ir.commands| && ir.commands != [] ==> //TODO: how to get user input
        match ir.commands[ir.pointer]
            case Inc(n) => 
                0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory| 
                && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                // && ((s.memory[s.pointer]+n >= 255) ==> s'.memory[s.pointer] == s.memory[s.pointer]+n%255)
                && s'.memory[s.pointer] == (s.memory[s.pointer]+n)%256 && ir_moved_up(ir, ir')
            case Move(n) => 
                0 <= s.pointer < |s.memory| && s.memory == s'.memory && 0 <= s'.pointer < |s.memory| 
                && ((s.pointer + n >= |s.memory|) ==> s'.pointer == |s.memory|-1)
                && ((s.pointer + n <= 0) ==> s'.pointer == 0)
                && ((0 <= s.pointer + n < |s.memory|) ==> s'.pointer == s.pointer+n) 
            case Jump(dest, direction) =>
                (ir_moved_up(ir, ir') && ir.commands == ir'.commands && ir.input == ir'.input && s == s') 
                //Because we want to compare the commands directly, if we are in an equivalent state at the start of the loop and the body is the same
                // we have an equivalent representation, we can thus just keep progressing normally
            case Print =>
                s.memory == s'.memory && s.pointer == s'.pointer && s'.output == s.output + [s.memory[s.pointer]as char] //Add more for printing?
                && ir_moved_up(ir, ir')
            case UserInput =>
                (
                    0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory| 
                    && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                    && (|ir.input| > 0 ==> s'.memory[s.pointer] == ir.input[0] as int && ir'.input==ir.input[1..])
                    && (|ir.input| == 0 ==> s'.memory[s.pointer] == ' ' as int && ir'.input==ir.input)
                    && ir_moved_up(ir, ir')
                )
        )
    }

    predicate max_steps(p: Program, s: State, p': Program, s': State)
    requires p.commands == p'.commands 
    decreases |p.commands| - p.pointer
    requires valid_program(p) && valid_program(p')
    requires state_reqs(s) && state_reqs(s') && valid_state(s, s') && aligned_programs(p, p')
    {
        (p.pointer == |p.commands| && p==p' && s==s') || (p.pointer < |p.commands| &&
        match p.commands[p.pointer]
            case '+' | '-' =>
                s.pointer == s'.pointer&&
                |s.memory| == |s'.memory| &&
                (p.pointer < p'.pointer)&&
                (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] in ['+', '-']))
                && (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] in ['+', '-'])))
                && (s'.memory[s.pointer] == (s.memory[s.pointer]+count_commands(p, p', ['+', '-']))%256)
                && (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i])
            case '>' | '<' =>
                (p.pointer < p'.pointer)&&
                (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] in ['>', '<']))
                && (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] in ['<', '>'])))
                && (s'.memory == s.memory)
                && (0 <= s.pointer+count_commands(p, p', ['>', '<']) < |s.memory| ==> s'.pointer == s.pointer + count_commands(p, p', ['>', '<']))
                && (0 > s.pointer+count_commands(p, p', ['>', '<']) ==> s'.pointer == 0)
                && (|s.memory|<= s.pointer+count_commands(p, p', ['>', '<']) ==> s'.pointer == |s.memory|-1)
            case ',' | '.' =>
                program_step(s, p, s', p')
            case '[' =>
            (0 <= s.pointer < |s.memory| && 0 <= s'.pointer < |s.memory| )
                && pointer_moved_up(p,p')
                // && (s.memory[s.pointer]== 0 ==> (p'.pointer > p.pointer && p'.commands[p'.pointer-1]== ']' && valid_loop(p.commands[p.pointer+1.. p'.pointer-1])))    //Need to add forall to make sure that at the soonest ]
            case ']' =>
                (
                    (0 <= s.pointer < |s.memory| && 0 <= s'.pointer <= |s.memory| )
                    && (pointer_moved_up(p, p'))
                    // && (s.memory[s.pointer] > 0 ==> (0 < p'.pointer < p.pointer && p'.commands[p'.pointer-1]== '[' && valid_loop(p.commands[p'.pointer.. p.pointer-1])))
                )
        )
    }


function count_commands(p: Program, p': Program, symbols: seq<char>): int
    requires p.pointer <= p'.pointer <= |p.commands|
    requires |symbols| == 2
    requires |p.commands| > 0
    requires aligned_programs(p, p')
    decreases p'.pointer-p.pointer
{
    if p.pointer == p'.pointer then 0
    // else if p.pointer + 1 >= p'.pointer then 0
    else
        assert p.pointer < |p.commands|;
        (if p.commands[p.pointer] in symbols then
            (if p.commands[p.pointer] == '+' then 1 else -1)
         else 0) +
         count_commands(p.(pointer := p.pointer + 1), p', symbols)
}


    ghost predicate program_k_max_steps(p: Program, s: State, p': Program, s': State, k: int)
    decreases k
    requires 0<= k
    requires valid_program(p)
    requires state_reqs(s)
    {
    if k==0 then
        p == p' && s == s' 
    else 
        exists p'': Program, s'': State:: (valid_state(s, s'') && state_reqs(s'') && aligned_programs(p, p'') && valid_program(p'') && max_steps(p, s, p'', s'') &&
        p.pointer <= |p.commands| && program_k_max_steps(p'', s'', p', s', k-1))
    }

    ghost predicate ir_k_steps(ir: IntermediateRep, s: State, ir': IntermediateRep, s': State, k: int)
    decreases k
    requires 0<= k
    // requires valid_program(p)
    requires 0 <= ir.pointer
    requires 0<= ir'.pointer
    requires state_reqs(s)
    requires valid_ir(ir)
    requires valid_input(ir.input)
    requires valid_ir(ir')
    requires valid_input(ir'.input)
    {
    if k==0 then
        ir == ir' && s == s' 
    else 
        exists ir'': IntermediateRep, s'': State :: (valid_state(s, s'') && state_reqs(s'') && in_sync_irs(ir, ir'') && valid_ir(ir'') && ir_step(ir, s, ir'', s'') && valid_input(ir''.input)&&
        ir_k_steps(ir'', s'', ir', s', k-1))
    }


}
