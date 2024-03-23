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

class out_spc700_t : public outctx_t
{
	out_spc700_t(void) : outctx_t(BADADDR) {} // not used
private:
	void out_dp(const op_t& x);
public:
	bool out_operand(const op_t& x);
	void out_insn(void);
};
CASSERT(sizeof(out_spc700_t) == sizeof(outctx_t));

DECLARE_OUT_FUNCS_WITHOUT_OUTMNEM(out_spc700_t)

 //----------------------------------------------------------------------
//static void out_spc700_t::out_dp(op_t& x)
void out_spc700_t::out_dp(const op_t& x)
{
	sel_t dp = get_sreg(insn.ea, rFp);
	if (dp != BADSEL)
	{
		ea_t ea = (dp << 8) | x.addr;

		//if ( dp != 0 )
		//  out_symbol('(');

		if (!out_name_expr(x, ea, BADADDR))
		{
			out_tagon(COLOR_ERROR);
			out_btoa /*		OutLong*/(ea, 16);
			out_tagoff(COLOR_ERROR);
			//QueueSet(Q_noName, cmd.ea);
			remember_problem(PR_NONAME, insn.ea);
		}

		//if ( dp != 0 )
		//{
		//  out_symbol(' ');
		//  out_symbol('-');
		//  out_symbol(' ');
		//  OutLong(dp << 8, 16);
		//  out_symbol(')');
		//}
	}
	else
	{
		out_value /*OutValue*/(x, OOF_ADDR | OOFS_NOSIGN | OOFW_8);
	}
}

//----------------------------------------------------------------------
//bool idaapi outop(op_t& x)
bool out_spc700_t::out_operand(const op_t& x)
{
	ea_t ea;
	switch (x.type)
	{
	case o_reg:
		out_register(ph.reg_names[x.reg]);
		break;
	case o_imm:
		out_symbol('#');
		out_value(x, 0);
		break;
	case o_near:
	case o_far:
	case o_mem:
		if (insn.indirect)
			out_symbol('(');
		ea = x.addr;
		if (!out_name_expr(x, ea, BADADDR))
		{
			out_tagon(COLOR_ERROR);
			out_btoa /*		OutLong*/(ea, 16);
			out_tagoff(COLOR_ERROR);
			//QueueSet(Q_noName, insn.ea);
			remember_problem(PR_NONAME, insn.ea);
		}
		if (insn.indirect)
			out_symbol(')');
		break;
	case o_phrase:
		switch (x.phrase)
		{
		case riX:
		case riY:
			out_symbol('(');
			out_register(x.phrase == riX ? ph.reg_names[rX] : ph.reg_names[rY]);
			out_symbol(')');
			break;
		case riXinc:
			out_symbol('(');
			out_register(ph.reg_names[rX]);
			out_symbol(')');
			out_symbol('+');
			break;
		default:
			goto err;
		}
		break;
	case o_displ:
		switch (x.phrase)
		{
		case rD:
			out_dp(x);
			break;
		case rDX:
		case rDY:
			out_dp(x);
			out_symbol('+');
			out_register(x.phrase == rDX ? ph.reg_names[rX] : ph.reg_names[rY]);
			break;
		case riDX:
			out_symbol('(');
			out_dp(x);
			out_symbol('+');
			out_register(ph.reg_names[rX]);
			out_symbol(')');
			break;
		case rDiY:
			out_symbol('(');
			out_dp(x);
			out_symbol(')');
			out_symbol('+');
			out_register(ph.reg_names[rY]);
			break;
		case rAbsX:
		case rAbsY:
			if (!out_name_expr(x, x.addr, BADADDR))
				out_value/* OutValue*/(x, OOF_ADDR | OOFS_NOSIGN | OOFW_16);
			out_symbol('+');
			out_register(x.phrase == rAbsX ? ph.reg_names[rX] : ph.reg_names[rY]);
			break;
		case rAbsXi:
			out_symbol('(');
			if (!out_name_expr(x, x.addr, BADADDR))
				out_value/* OutValue*/(x, OOF_ADDR | OOFS_NOSIGN | OOFW_16);
			out_symbol('+');
			out_register(ph.reg_names[rX]);
			out_symbol(')');
			break;
		case rDbitnot:
			out_symbol('/');
			// fall through
		case rDbit:
			if (!out_name_expr(x, x.addr, BADADDR))
				out_value/* OutValue*/(x, OOF_ADDR | OOFS_NOSIGN | OOFW_16);
			out_symbol('.');
			out_value/* OutValue*/(x, 0);
			break;
		case rTCall:
			out_btoa /*OutLong*/(x.value, 10);
			break;
		case rPCall:
			out_btoa /*OutLong*/(x.value, 16);
			break;
		default:
			goto err;
		}
		break;
	case o_void:
		return 0;
	default:
	err:
		warning("out: %a: bad optype %d", insn.ea, x.type);
		break;
	}
	return 1;
}

//----------------------------------------------------------------------
inline bool forced_print(ea_t ea, int /*reg*/)
{
	return is_func(get_flags(ea));
}

//----------------------------------------------------------------------
//void idaapi assumes(ea_t ea)
void    idaapi assumes(outctx_t& ctx, ea_t ea)
{
	char buf[MAXSTR];
	char* ptr = buf;
	char* end = buf + sizeof(buf);
	for (int reg = ph.reg_first_sreg/*  .regFirstSreg*/; reg <= ph.reg_last_sreg /* .regLastSreg*/; reg++)
	{
		if (reg == rCs || reg == rDs)
			continue;
		sreg_range_t /*segreg_area_t*/ srarea;
		get_sreg_range /*get_srarea2*/(&srarea, ea, reg);
		sreg_range_t /*segreg_area_t*/ prev;
		bool prev_exists = get_sreg_range /*get_srarea2*/(&prev, ea - 1, reg);
		// if 'prev' does not exist, force to print because we are at
		// the beginning of the segment
		sel_t curval = srarea.val;
		sel_t prevval = prev_exists ? prev.val : curval - 1;
		if (curval != prevval || forced_print(ea, reg))
		{
			if (reg == rFp)
			{
				ctx.gen_cmt_line("P=%d", curval);
			}
			else
			{
				if (ptr != buf)
					APPCHAR(ptr, end, ' ');
				ptr += qsnprintf(ptr, end - ptr, "%s=%a", ph.reg_names[reg], curval);
			}
		}
	}
	if (ptr != buf)
		ctx.gen_cmt_line("%s", buf);
}

//----------------------------------------------------------------------
//void idaapi out(void)
void out_spc700_t::out_insn(void)
{
#ifdef IDA61
	char buf[MAXSTR];

	init_output_buffer(buf, sizeof(buf));
	if (inf.s_showbads
		&& cmd.Op1.type == o_displ
		&& (cmd.Op1.phrase == rX || cmd.Op1.phrase == rY)
		&& cmd.Op1.value == uchar(cmd.Op1.value))
	{
		OutBadInstruction();
	}

	OutMnem();
#else
	out_mnemonic();
#endif
	out_one_operand(0);
	if (insn.Op2.type != o_void)
	{
		out_symbol(',');
		out_char(' ');
		out_one_operand(1);
	}
#ifdef IDA61
	if (isVoid(cmd.ea, uFlag, 0))
		OutImmChar(cmd.Op1);

	term_output_buffer();
	gl_comm = 1;
	MakeLine(buf);
#else
	out_immchar_cmts();
	flush_outbuf();
#endif
}

//--------------------------------------------------------------------------
//void idaapi header(void)
void idaapi header(outctx_t& ctx)
{
	ctx.gen_cmt_line("%s Processor:        %s", ash.cmnt, inf.procname);
	ctx.gen_cmt_line("%s Target assembler: %s", ash.cmnt, ash.name);
	if (ash.header != NULL)
		for (const char* const* ptr = ash.header; *ptr != NULL; ptr++)
			ctx.flush_buf/*  MakeLine*/(*ptr, 0);
}

//--------------------------------------------------------------------------
//void idaapi segstart(ea_t ea)
void idaapi segstart(outctx_t& ctx, segment_t* seg)
{
	//segment_t* Sarea = getseg(ea);
	ea_t ea = ctx.insn_ea;
	qstring name; //char name[MAXNAMELEN];
	get_visible_segm_name(&name, seg); //get_segm_name(Sarea, name, sizeof(name));
	if (ash.uflag & UAS_SECT)
	{
		ctx.gen_printf/*printf_line*/(0, COLSTR("%s: .section", SCOLOR_ASMDIR), name);
	}
	else
	{
		ctx.gen_printf/*printf_line*/(inf.indent, COLSTR("%s.segment %s", SCOLOR_ASMDIR),
			(ash.uflag & UAS_NOSEG) ? ash.cmnt : "",
			name);
		if (ash.uflag & UAS_SELSG)
			ctx.flush_buf/*  MakeLine*/(name.c_str(), inf.indent);
		if (ash.uflag & UAS_CDSEG)
			ctx.flush_buf/*  MakeLine*/(COLSTR("CSEG", SCOLOR_ASMDIR), inf.indent);  // XSEG - eXternal memory
	}
	//if (inf.s_org)
	if ((inf.outflags & OFLG_GEN_ORG) != 0)
	{
		//ea_t org = ea - get_segm_base(Sarea);
		ea_t org = ea - get_segm_base(seg);
		if (org != 0)
		{
			char buf[MAX_NUMBUF];
			btoa(buf, sizeof(buf), org);
			ctx.gen_printf/*printf_line*/(inf.indent, COLSTR("%s %s", SCOLOR_ASMDIR), ash.origin, buf);
		}
	}
}

//--------------------------------------------------------------------------
//void idaapi footer(void)
void idaapi footer(outctx_t& ctx)
{
	char buf[MAXSTR];
	if (ash.end != NULL)
	{
		ctx.gen_empty_line(); //MakeNull();
		char* ptr = buf;
		char* end = buf + sizeof(buf);
		APPEND(ptr, end, ash.end);
		qstring name;
		if (get_colored_name(&name, inf.start_ea /*beginEA*/) > 0)
		{
			if (ash.uflag & UAS_NOENS)
				APPEND(ptr, end, ash.cmnt);
			APPCHAR(ptr, end, ' ');
			APPEND(ptr, end, name.begin());
		}
		ctx.flush_buf/*  MakeLine*/(buf, inf.indent);
	}
	else
	{
		ctx.gen_cmt_line/*  gen_cmt_line*/("end of file");
	}
}
