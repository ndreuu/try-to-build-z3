//------------------------------------------------------------------------------
// <auto-generated>
//     This code was generated by a tool.
//     ANTLR Version: 4.10.1
//
//     Changes to this file may cause incorrect behavior and will be lost if
//     the code is regenerated.
// </auto-generated>
//------------------------------------------------------------------------------

// Generated from /home/andrew/RiderProjects/adt-solver/RedlogParser/RedTrace.g4 by ANTLR 4.10.1

// Unreachable code detected
#pragma warning disable 0162
// The variable '...' is assigned but its value is never used
#pragma warning disable 0219
// Missing XML comment for publicly visible type or member '...'
#pragma warning disable 1591
// Ambiguous reference in cref attribute
#pragma warning disable 419

using Antlr4.Runtime.Misc;
using Antlr4.Runtime.Tree;
using IToken = Antlr4.Runtime.IToken;

/// <summary>
/// This interface defines a complete generic visitor for a parse tree produced
/// by <see cref="RedTraceParser"/>.
/// </summary>
/// <typeparam name="Result">The return type of the visit operation.</typeparam>
[System.CodeDom.Compiler.GeneratedCode("ANTLR", "4.10.1")]
[System.CLSCompliant(false)]
public interface IRedTraceVisitor<Result> : IParseTreeVisitor<Result> {
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.prog"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitProg([NotNull] RedTraceParser.ProgContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.expr"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitExpr([NotNull] RedTraceParser.ExprContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.body"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitBody([NotNull] RedTraceParser.BodyContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.mul"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitMul([NotNull] RedTraceParser.MulContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.ncgong"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitNcgong([NotNull] RedTraceParser.NcgongContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.factor"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitFactor([NotNull] RedTraceParser.FactorContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.power"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitPower([NotNull] RedTraceParser.PowerContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.num"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitNum([NotNull] RedTraceParser.NumContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.number"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitNumber([NotNull] RedTraceParser.NumberContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.id"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitId([NotNull] RedTraceParser.IdContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.and"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitAnd([NotNull] RedTraceParser.AndContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.or"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitOr([NotNull] RedTraceParser.OrContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.equal"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitEqual([NotNull] RedTraceParser.EqualContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.gr"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitGr([NotNull] RedTraceParser.GrContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.ls"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitLs([NotNull] RedTraceParser.LsContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.neq"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitNeq([NotNull] RedTraceParser.NeqContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.leq"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitLeq([NotNull] RedTraceParser.LeqContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.geq"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitGeq([NotNull] RedTraceParser.GeqContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.ball"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitBall([NotNull] RedTraceParser.BallContext context);
	/// <summary>
	/// Visit a parse tree produced by <see cref="RedTraceParser.nil"/>.
	/// </summary>
	/// <param name="context">The parse tree.</param>
	/// <return>The visitor result.</return>
	Result VisitNil([NotNull] RedTraceParser.NilContext context);
}
