/*
 *      Interactive disassembler (IDA).
 *      Version 3.05
 *      Copyright (c) 1990-95 by Ilfak Guilfanov.
 *      ALL RIGHTS RESERVED.
 *                              FIDO:   2:5020/209
 *                              E-mail: ig@estar.msk.su
 *
 */

#include "spc700.hpp"

static bool flow;
//------------------------------------------------------------------------
//static void doImmdValue(insn_t& cmd) //void)
//{
//	set_immd(cmd.ea);
//}

//----------------------------------------------------------------------
static void handle_operand(insn_t& cmd, op_t& x, bool read_access)
{
	ea_t ea;
	dref_t dreftype;
	switch (x.type)
	{
	case o_void:
	case o_reg:
	case o_phrase:
		break;

	case o_imm:
		QASSERT(557, read_access);
		dreftype = dr_O;
	MAKE_IMMD:
		set_immd(cmd.ea); //doImmdValue(cmd);
		if (is_off(get_flags(cmd.ea)  /*uFlag*/, x.n))
			cmd.add_off_drefs /*ua_add_off_drefs*/(x, dreftype, 0);
		break;

	case o_displ:
		dreftype = read_access ? dr_R : dr_W;
		switch (x.phrase)
		{
		case rD:        // "dp"
		case rDX:       // "dp, X"
		case rDY:       // "dp, Y"
		case riDX:      // "(dp, X)"
		case rDiY:      // "(dp,n), Y"
		{
			sel_t dp = get_sreg(cmd.ea, rFp);
			if (dp != BADSEL)
			{
				ea = to_ea(map_data_ea /*dataSeg_op*/(cmd, x.n), (dp << 8) | x.addr);
				goto MAKE_DREF;
			}
			else
			{
				goto MAKE_IMMD;
			}
		}

		case rAbsX:     // "abs, X"
		case rAbsY:     // "abs, Y"
		case rAbsXi:    // "(abs,X)"
		case rDbit:     // "abs.n"
		case rDbitnot:  // "/abs.n"
			//ea = to_ea(dataSeg_op(x.n), x.addr);
			ea = to_ea(map_data_ea(cmd, x.n), x.addr);
			goto MAKE_DREF;

		case rTCall:    // "tcall n"
		case rPCall:    // "pcall n"
			ea = x.addr;
			goto MAKE_CREF;

		default:
			goto MAKE_IMMD;
		}
		break;

	case o_mem:
		ea = to_ea(map_data_ea(cmd, x.n), x.addr);
	MAKE_DREF:
		//ua_dodata2(x.offb, ea, x.dtype);
		cmd.create_op_data(x.offb, ea, x.dtype);
#ifdef IDA61
		if (!read_access)
			doVar(ea);
#endif
		//ua_add_dref(x.offb, ea, read_access ? dr_R : dr_W);
		cmd.add_dref(x.offb, ea, read_access ? dr_R : dr_W);
		break;

	case o_near:
	case o_far:
	{
		if (x.type == o_near)
		{
			ea_t segbase = map_code_ea(cmd, x.addr, x.n);
			ea = to_ea(segbase, x.addr);
		}
		else
		{
			ea = x.addr;
		}

	MAKE_CREF:
		bool iscall = has_insn_feature(cmd.itype, CF_CALL);
		cref_t creftype = x.type == o_near
			? iscall ? fl_CN : fl_JN
			: iscall ? fl_CF : fl_JF;
		cmd.add_cref /* ua_add_cref*/(x.offb, ea, creftype);
		if (flow && iscall)
			flow = func_does_return(ea);
	}
	break;

	default:
		INTERR(558);
	}
}

//----------------------------------------------------------------------
// Mark the jump table content as a offset, and mark the destination address as code
// Note: sometimes the real table is located at another address (e.g. Super Mario World)
static void handle_jump_table(ea_t /*jtable_addr*/)
{
	// TODO: mark jump table
}

//----------------------------------------------------------------------
//int idaapi emu(void)
int     idaapi emu(insn_t& cmd)
{
	uint32 Feature = cmd.get_canon_feature();
	flow = ((Feature & CF_STOP) == 0);

	if (Feature & CF_USE1) handle_operand(cmd, cmd.ops[0] /*.Op1*/, 1);
	if (Feature & CF_USE2) handle_operand(cmd, cmd.ops[1] /*.Op2*/, 1);
	if (Feature & CF_CHG1) handle_operand(cmd, cmd.ops[0] /*.Op1*/, 0);
	if (Feature & CF_CHG2) handle_operand(cmd, cmd.ops[0] /*.Op2*/, 0);
	if (Feature & CF_JUMP) remember_problem(PR_JUMP /*Q_jumps*/, cmd.ea);

	uint8 code = get_byte(cmd.ea);
	const struct opcode_info_t& opinfo = get_opcode_info(code);

	if (opinfo.itype == SPC_jmp)
	{
		if (opinfo.addr == ABS_IX_INDIR) {
			remember_problem(PR_JUMP /*Q_jumps*/, cmd.ea);

			handle_jump_table(cmd.Op1.addr);
		}
	}

	if (flow)
		cmd.add_cref            /*ua_add_cref*/(0, cmd.ea + cmd.size, fl_F);

	switch (cmd.itype)
	{
	case SPC_setp:
		split_sreg_range /*split_srarea*/(cmd.ea + 1, rFp, 1, SR_auto);
		break;

	case SPC_clrp:
		split_sreg_range /*split_srarea*/(cmd.ea + 1, rFp, 0, SR_auto);
		break;

	case SPC_jmp:
	case SPC_call:
	{
		if (cmd.Op1.full_target_ea)
		{
			ea_t ftea = cmd.Op1.full_target_ea;
			split_sreg_range/*split_srarea*/(ftea, rFp, get_sreg(cmd.ea, rFp), SR_auto);
		}
	}
	break;

	case SPC_php:
		// TODO: backtrack stack and update rFp
		break;

	case SPC_plp:
		// TODO: backtrack stack and update rFp
		break;
	}

	return 1;
}
