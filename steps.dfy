include "common.dfy"
module Steps{
    import opened Common

    predicate program_step(s: State, p: Program, s': State, p': Program)
    
    decreases |p.commands|-p.pointer
    requires valid_program(p) && valid_program(p') 
    requires state_reqs(s)
    {
        0 <= p.pointer < |p.commands| && 0 <= p'.pointer <= |p'.commands| && p.commands == p'.commands && 
        p.commands != [] ==> 
        match p.commands[p.pointer]
            case '+' => 
                s.pointer == s'.pointer&&
                |s.memory| == |s'.memory| && s'.output == s.output&&
                pointer_moved_up(p, p') &&
                (s'.memory[s.pointer] == (s.memory[s.pointer]+ 1)%256)
                && (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i])

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
                s == s' && p.commands == p'.commands
                && ((s.memory[s.pointer] > 0) ==> pointer_moved_up(p,p'))
                && (s.memory[s.pointer]== 0 ==> (p'.pointer > p.pointer && p'.commands[p'.pointer-1]== ']' && valid_loop(p.commands[p.pointer+1.. p'.pointer-1])))    //Need to add forall to make sure that at the soonest ]
            case '.' =>
                s.memory == s'.memory && s.pointer == s'.pointer //Add more for printing?
                // && (0 <= s.pointer < |s.memory| && 0 <= s'.pointer < |s.memory| )
                && pointer_moved_up(p, p')
                && s'.output == s.output + [s.memory[s.pointer] as char]
            case ']' => 
                (
                    s == s' && p.commands == p'.commands
                    && ((s.memory[s.pointer] == 0) ==> pointer_moved_up(p, p'))
                    && (s.memory[s.pointer] > 0 ==> (0 < p'.pointer <=p.pointer && p'.commands[p'.pointer-1]== '[' && valid_loop(p.commands[p'.pointer.. p.pointer])))
                )
            case ',' =>
                (
                    0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory| 
                    && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                    && (|p.input| > 0 ==> (s'.memory[s.pointer] == p.input[0] as int && p'.input == p.input[1..]))
                    && (|p.input| == 0 ==> (p'.input == p.input && s'.memory[s.pointer]==' ' as int))
                    && pointer_moved_up(p, p')&& s'.output == s.output
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
        (ir.pointer < |ir.commands| && ir.commands != [] ==> 
        match ir.commands[ir.pointer]
            case Inc(n) => 
                0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory|  && s.output == s'.output
                && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                && s'.memory[s.pointer] == (s.memory[s.pointer]+n)%256 && ir_moved_up(ir, ir')
            case Move(n) => 
                0 <= s.pointer < |s.memory| && s.memory == s'.memory && 0 <= s'.pointer < |s.memory| 
                && ((s.pointer + n >= |s.memory|) ==> s'.pointer == |s.memory|-1)
                && ((s.pointer + n <= 0) ==> s'.pointer == 0) && s.output == s'.output
                && ((0 <= s.pointer + n < |s.memory|) ==> s'.pointer == s.pointer+n) 
            case Jump(dest, direction) =>
                s == s' && ir.input == ir'.input && ir.commands == ir'.commands &&
                ((direction && (
                    (s.memory[s.pointer] > 0 && ir'.pointer == ir.pointer+1)
                    ||
                    (s.memory[s.pointer]==0 && ir'.pointer == dest+1)

                )) ||
                (!direction && (
                    (s.memory[s.pointer] > 0 && ir'.pointer == dest+1)
                    ||
                    (s.memory[s.pointer]==0 && ir'.pointer == ir.pointer+1)
                ))
                )
                // (ir_moved_up(ir, ir') && ir.commands == ir'.commands && ir.input == ir'.input && s == s') 
            case Print =>
                s.memory == s'.memory && s.pointer == s'.pointer && s'.output == s.output + [s.memory[s.pointer]as char] //Add more for printing?
                && ir_moved_up(ir, ir')
            case UserInput =>
                (
                    0 <= s.pointer < |s.memory| && s.pointer == s'.pointer && |s.memory| == |s'.memory| 
                    && (forall i :: 0 <= i < |s.memory| && i != s.pointer ==> (s.memory[i] == s'.memory[i]))
                    && (|ir.input| > 0 ==> s'.memory[s.pointer] == ir.input[0] as int && ir'.input==ir.input[1..])
                    && (|ir.input| == 0 ==> s'.memory[s.pointer] == ' ' as int && ir'.input==ir.input)
                    && ir_moved_up(ir, ir') && s'.output == s.output
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
            case '+' =>
                s.pointer == s'.pointer&&
                |s.memory| == |s'.memory| && s'.output == s.output&&
                (p.pointer < p'.pointer)&&
                (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == '+'))
                && (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == '+')))
                && (s'.memory[s.pointer] == (s.memory[s.pointer]+ p'.pointer-p.pointer)%256)
                && (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i])
            case '-' =>
                s.pointer == s'.pointer&&
                |s.memory| == |s'.memory| && s'.output == s.output&&
                (p.pointer < p'.pointer)&&
                (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == '-'))
                && (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == '-')))
                && (s'.memory[s.pointer] == (s.memory[s.pointer]+ p.pointer-p'.pointer)%256)
                && (forall i:: (0 <= i < |s.memory|  && i != s.pointer) ==> s.memory[i] == s'.memory[i])
            case '>' =>
                |s.memory| == |s'.memory| && s'.output == s.output&&
                (p.pointer < p'.pointer)&&
                (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == '>'))
                && (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == '>')))
                && (s'.memory == s.memory)
                && (0 <= s.pointer+p'.pointer-p.pointer < |s.memory| ==> s'.pointer == s.pointer + p'.pointer-p.pointer)
                // && (0 > s.pointer+count_commands(p, p', ['>', '<']) ==> s'.pointer == 0)
                && ((|s.memory|<= s.pointer+p'.pointer-p.pointer) ==> s'.pointer == |s.memory|-1)
            case '<' =>
                |s.memory| == |s'.memory| && s'.output == s.output&&
                (p.pointer < p'.pointer)&&
                (forall i:: (p.pointer<=i< p'.pointer ==>  p.commands[i] == '<'))
                && (p'.pointer == |p.commands| || (p'.pointer < |p.commands| ==> !(p.commands[p'.pointer] == '<')))
                && (s'.memory == s.memory)
                && (0 <= s.pointer-p'.pointer+p.pointer < |s.memory| ==> s'.pointer == s.pointer - p'.pointer+p.pointer)
                // && (0 > s.pointer+count_commands(p, p', ['>', '<']) ==> s'.pointer == 0)
                && ((0 >= s.pointer-p'.pointer+p.pointer) ==> s'.pointer == 0)
            case ',' | '.' =>
                program_step(s, p, s', p')
            case '[' =>
                (s == s' && p.commands == p'.commands
                && ((s.memory[s.pointer] > 0) ==> pointer_moved_up(p,p'))
                && (s.memory[s.pointer]== 0 ==> (p'.pointer > p.pointer && p'.commands[p'.pointer-1]== ']' && valid_loop(p.commands[p.pointer+1.. p'.pointer-1]))))    //Need to add forall to make sure that at the soonest ]
            case ']' =>
                program_step(s, p, s', p')
        )
    }



    ghost predicate program_k_max_steps(p: Program, s: State, p': Program, s': State, k: int)
    requires 0<= k
    requires valid_program(p)
    requires valid_program(p')
    requires aligned_programs(p, p')
    requires state_reqs(s) 
    requires state_reqs(s')
    requires valid_state(s, s')
    {
        (k < |Changes(p)| ==> 0<=Changes(p)[k] < |p.commands| && max_steps(Program(p.commands, Changes(p)[k], p.input), s, p', s'))
        &&
        (k >= |Changes(p)| ==> max_steps(Program(p.commands, |p.commands|, p.input), s, p', s'))
    }

}
