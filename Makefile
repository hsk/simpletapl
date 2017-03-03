# :- style_check(-singleton).

run:
	swipl arith.pl > results/arith_result.txt
	diff results/arith_result.txt results/arith_expected.txt
	swipl farith.pl > results/farith_result.txt
	diff results/farith_result.txt results/farith_expected.txt
	swipl fomarith.pl > results/fomarith_result.txt
	diff results/fomarith_result.txt results/fomarith_expected.txt
	swipl untyped.pl > results/untyped_result.txt
	diff results/untyped_result.txt results/untyped_expected.txt
	swipl fulluntyped.pl > results/fulluntyped_result.txt
	diff results/fulluntyped_result.txt results/fulluntyped_expected.txt
	swipl tyarith.pl > results/tyarith_result.txt
	diff results/tyarith_result.txt results/tyarith_expected.txt
	swipl simplebool.pl > results/simplebool_result.txt
	diff results/simplebool_result.txt results/simplebool_expected.txt
	swipl fullsimple.pl > results/fullsimple_result.txt
	diff results/fullsimple_result.txt results/fullsimple_expected.txt
	swipl fullref.pl > results/fullref_result.txt
	diff results/fullref_result.txt results/fullref_expected.txt
	swipl fullerror.pl > results/fullerror_result.txt
	diff results/fullerror_result.txt results/fullerror_expected.txt
	swipl bot.pl > results/bot_result.txt
	diff results/bot_result.txt results/bot_expected.txt
	swipl rcdsubbot.pl > results/rcdsubbot_result.txt
	diff results/rcdsubbot_result.txt results/rcdsubbot_expected.txt
	swipl fullsub.pl > results/fullsub_result.txt
	diff results/fullsub_result.txt results/fullsub_expected.txt
	swipl equirec.pl > results/equirec_result.txt
	diff results/equirec_result.txt results/equirec_expected.txt
	swipl fullequirec.pl > results/fullequirec_result.txt
	diff results/fullequirec_result.txt results/fullequirec_expected.txt
	swipl fullisorec.pl > results/fullisorec_result.txt
	diff results/fullisorec_result.txt results/fullisorec_expected.txt
	swipl reconbase.pl > results/reconbase_result.txt
	diff results/reconbase_result.txt results/reconbase_expected.txt
#	swipl recon.pl > results/recon_result.txt
#	diff results/recon_result.txt results/recon_expected.txt
#	swipl fullrecon.pl > results/fullrecon_result.txt
#	diff results/fullrecon_result.txt results/fullrecon_expected.txt
	swipl fullpoly.pl > results/fullpoly_result.txt
	diff results/fullpoly_result.txt results/fullpoly_expected.txt
	swipl purefsub.pl > results/purefsub_result.txt
	diff results/purefsub_result.txt results/purefsub_expected.txt
	swipl fullfsub.pl > results/fullfsub_result.txt
	diff results/fullfsub_result.txt results/fullfsub_expected.txt
	swipl fullfsubref.pl > results/fullfsubref_result.txt
	diff results/fullfsubref_result.txt results/fullfsubref_expected.txt
#	swipl fomega.pl > results/fomega_result.txt
#	diff results/fomega_result.txt results/fomega_expected.txt
#	swipl fomsub.pl > results/fomsub_result.txt
#	diff results/fomsub_result.txt results/fomsub_expected.txt
#	swipl fullomega.pl > results/fullomega_result.txt
#	diff results/fullomega_result.txt results/fullomega_expected.txt
#	swipl fullfomsub.pl > results/fullfomsub_result.txt
#	diff results/fullfomsub_result.txt results/fullfomsub_expected.txt
#	swipl fullfomsubref.pl > results/fullfomsubref_result.txt
#	diff results/fullfomsubref_result.txt results/fullfomsubref_expected.txt
#	swipl fullupdate.pl > results/fullupdate_result.txt
#	diff results/fullupdate_result.txt results/fullupdate_expected.txt
#	swipl joinexercise.pl > results/joinexercise_result.txt
#	diff results/joinexercise_result.txt results/joinexercise_expected.txt
	swipl letexercise.pl > results/letexercise_result.txt
	diff results/letexercise_result.txt results/letexercise_expected.txt


gen:
	swipl arith.pl > results/arith_expected.txt
	swipl farith.pl > results/farith_expected.txt
	swipl fomarith.pl > results/fomarith_expected.txt
	swipl untyped.pl > results/untyped_expected.txt
	swipl fulluntyped.pl > results/fulluntyped_expected.txt
	swipl tyarith.pl > results/tyarith_expected.txt
	swipl simplebool.pl > results/simplebool_expected.txt
	swipl fullsimple.pl > results/fullsimple_expected.txt
	swipl fullref.pl > results/fullref_expected.txt
	swipl fullerror.pl > results/fullerror_expected.txt
	swipl bot.pl > results/bot_expected.txt
	swipl rcdsubbot.pl > results/rcdsubbot_expected.txt
	swipl fullsub.pl > results/fullsub_expected.txt
	swipl equirec.pl > results/equirec_expected.txt
	swipl fullequirec.pl > results/fullequirec_expected.txt
	swipl fullisorec.pl > results/fullisorec_expected.txt
	swipl reconbase.pl > results/reconbase_expected.txt
#	swipl recon.pl > results/recon_expected.txt
#	swipl fullrecon.pl > results/fullrecon_expected.txt
	swipl fullpoly.pl > results/fullpoly_expected.txt
	swipl purefsub.pl > results/purefsub_expected.txt
	swipl fullfsub.pl > results/fullfsub_expected.txt
	swipl fullfsubref.pl > results/fullfsubref_expected.txt
#	swipl fomega.pl > results/fomega_expected.txt
#	swipl fomsub.pl > results/fomsub_expected.txt
#	swipl fullomega.pl > results/fullomega_expected.txt
#	swipl fullfomsub.pl > results/fullfomsub_expected.txt
#	swipl fullfomsubref.pl > results/fullfomsubref_expected.txt
#	swipl fullupdate.pl > results/fullupdate_expected.txt
#	swipl joinexercise.pl > results/joinexercise_expected.txt
	swipl letexercise.pl > results/letexercise_expected.txt
clean:
	rm -rf results/*_result.txt
