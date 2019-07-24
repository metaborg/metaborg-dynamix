package lang.dynamix.strategies;

import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.LoggerUtils;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.terms.StrategoString;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

public class dnx_log_0_2 extends Strategy {
	private static final ILogger LOGGER = LoggerUtils.logger("Dynamix");
	public static dnx_log_0_2 instance = new dnx_log_0_2();

	@Override
	public IStrategoTerm invoke(Context context, IStrategoTerm current, IStrategoTerm lvl, IStrategoTerm msg) {
		String level   = ((StrategoString) lvl).stringValue();
		String message = ((StrategoString) msg).stringValue();
		
		switch (level) {
		  case "INFO":  LOGGER.info(message);  break;
		  case "WARN":  LOGGER.warn(message);  break;
		  case "ERROR": LOGGER.error(message); break;
		  default: return null;
		}
		return current;
	}
}
