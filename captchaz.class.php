<?php
	class Captchaz
	{
		/*
		 * Captchaz v0.1 <http://dev.kakaopor.hu/captchaz>
		 * Created by Gabor Heja, 2008
		 *
		 * This program is free software: you can redistribute it and/or modify
		 * it under the terms of the GNU General Public License as published by
		 * the Free Software Foundation, either version 3 of the License, or
		 * (at your option) any later version.
		 * 
		 * This program is distributed in the hope that it will be useful,
		 * but WITHOUT ANY WARRANTY; without even the implied warranty of
		 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
		 * GNU General Public License for more details.
		 * 
		 * You should have received a copy of the GNU General Public License
		 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
		 *
		 * Requires PHP + GD (with TTF support)
		 *
		 * The words were collected from random pages of the English
		 * Wikipedia <http://en.wikipedia.org/>
		 *
		 * The font was downloaded from WebpagePublicity.com
		 * <http://www.webpagepublicity.com/>
		 *
		 */
		
		static public function Generate($realm="captcha")
		{
			// a list of words
			$wordlist = "aberdeen ability aboard abortion abraham abroad absence absolute academic academy accept accepted access accessed accident account accounts accused achieve achieved acoustic acquired across acting action actions active activist activity actors actress actual actually adapted adding addition address adelaide adjacent admiral admitted adopted adrian adults advance advanced advice advocate aerial affair affairs affected africa african against agencies agency agents agreed aircraft airline airlines airport airports airways alabama alaska albany albert alberta albion albums alcohol alfred algeria alleged alliance allied allies allison allmusic allowed allowing allows almost already although altitude alumni always amateur america american americas amongst amount amounts analysis anatomy anchor ancient anderson andrea andreas andrew andrews angeles angelo angels anglican angola animal animalia animals animated annual annually another answer anthony antonio anyone anything apparent appeal appear appeared appears applied approach approval approved arabia arabic archive archives arctic argued argument arizona arkansas armenia armenian arnold around arranged arrest arrested arrival arrived arrives arsenal arthur article articles artist artistic artists aspect aspects assault assembly assets assigned assist assisted assumed asteroid athens athlete athletic atlanta atlantic atomic attached attack attacked attacks attempt attempts attend attended attitude attorney auburn auckland audience august augustus austin austria austrian author authors autumn avenue average aviation awarded awards bachelor backing bailey balance baldwin ballet banking banned baptist barbara barnes baronet baseball batman battery batting battle battles beating beatles beaumont beauty became because become becomes becoming before begins behavior behind beijing belarus belfast belgian belgium belief beliefs believe believed believes belize belongs benefit benefits bengal benjamin bennett benson berkeley berlin bermuda bernard besides better between beyond biggest billion binding binomial biology birthday births bishop bishops blocks boards bodies boeing bomber bombing bonnet border borders borough bosnia boston bottom bought boundary bowling boxing bradford bradley branch branches brands braves brazil breaking breaks bridge bridges briefly brigade bright bringing brings brisbane bristol britain british broadway broken bronze brooklyn brooks brother brothers brought browser buddha buddhism buddhist budget buenos buffalo builder building bulgaria bullet bureau burial buried burning burton business butler cabinet calendar calgary called calling camera cameron campaign campbell campus canada canadian cancer cannon cannot canton canyon capable capacity capita capital capitol captain capture captured carbon cardiff cardinal career carlos carolina caroline carried carrier carries carroll carrying carter cartoon casino castle catalog category catholic cattle caught caused causes causing cavalry ceased celtic cemetery census center centers central centre centres century ceremony certain chairman chamber champion chance change changed changes changing channel channels chapel chapelle chapman chapter chapters charge charged charges charity charles charlie charter charts chatham chemical cherry cheshire chester chicago chiefs children chinese choice choose chordata chorus chosen christ church churches cinema circle circuit circus citation cities citizen citizens civilian claimed claiming claims claire clarke classes classic classics claude cleanup clearly client climate clinical clinton closed closely closer closing clothing coaches coaching coastal coffee coleman college colleges collins colombia colonel colonial colonies colony colorado colors colour colours columbia columbus column combat combined comedian comedy comics coming command commands comments commerce common commonly commons commune communes compact company compared compete competed complete complex composed composer compound computer concept concepts concern concerns concert concerto concerts concrete conduct conflict confused congress connor consider consists constant consumer contact contain contains content contents contest context continue contract contrast control controls cooper copies copper cornell corner cornwall correct cotton council counted counter counties country county couple couples course courses courts cousin coverage covered covering covers crater crawford create created creating creation creative creator creature credit credited credits cricket crimes criminal crisis critic critical critics croatia croatian crossing cruise cruiser crystal cuisine cultural culture cultures currency current curtis custom customer customs cutting cycling cylinder cyprus dakota dallas damage damaged dancer dancing danger daniel danish database dating daughter davies deaths debate debuted decade decades december decide decided decides decision declared decline declined defeat defeated defence defender defense defined defunct degree degrees delaware deletion delivery demand democrat denied denmark dennis density denver depicted deputy derived descent describe desert design designed designer designs desire despite destiny destroy detail detailed details detroit develop device devices devoted dialogue diameter diamond diesel digital diocese direct directed directly director disaster discover discuss disease diseases disney display dispute disputed distance distinct district diverse divided divine division doctor doctrine document dodgers dollar dollars domain domestic dominant donald double doubles douglas download downtown drafted dragon dragons dramatic drawing dreams drinking driven driver drivers driving dropped drummer dublin duchess duncan duration durham during duties dynamic dynasty eagles earlier earliest earned easily eastern eating ecology economic economy ecuador edited editing edition editions editor editors edmonton edmund educated edward edwards effect effects effort efforts egyptian eighth either elected election electric element elements eleven eleventh elliott embassy emerged emperor empire employed empress endemic ending enemies energy engaged engine engineer engines england english enjoyed enough ensemble ensure entered entering entire entirely entitled entrance entries enzyme episode episodes equation equipped ernest escape essays estate estates estonia ethics ethiopia ethnic eugene europe european evening events everyone evidence exactly example examples except exchange executed exercise existed existing exists expand expanded expected expert explain explains exposed exposure express extended extent external extinct extreme facility facing factor factors factory faculty failed failure fairly fallen falling familiar families family famous fantasy farmer farmers farming fashion faster father favorite feature featured features february federal feeling feelings fellow female females fernando festival fiction fields fifteen fighter fighters fighting figure figures filled filmed finally finals finance finding finger finish finished finland finnish fisher fishing fitted fleming fletcher flight flights florence florida flower flowers flying focused follow followed follows fontaine football forced forces foreign forest forests forever formal formally format formats formed former formerly forming formula fortune forward foster fought founded founder founding fourth france francis franco franklin fraser freedom french frequent friday friend friendly friends frontier function funding funeral further future gabriel gained galaxy gallery gameplay garden gardens gardner gazette gender general genesis genetic geneva geology george georges georgia georgian gerald germain german germans germany getting giants gibson gilbert giovanni giving glasgow global goddess golden google gordon gospel gothic governor grades graduate graham grammar grammy grande grandson granted graphic graphics greater greatest greatly greece greene gregory ground grounds groups growing growth guardian guards guests guilty guinea guitar guitars gundam habitat halifax hamburg hamilton hamlet hammer hampton handbook handed handle hanover happened harbor harbour hardware harold harper harris harrison harvard harvey having hawaii headed health hearing hearts heaven heavily hebrew height heights helped helping herald herbert heritage hermann heroes herself hidden higher highest highland highly highway highways himself hispanic historic history hockey holding holiday holland holmes homepage honorary honors honour honours hopkins horror horses hospital hosted houses housing houston howard however hudson hughes humans hundred hundreds hungary hunter hunting husband iceland identify identity illegal illinois illness images impact imperial improve improved inches incident include included includes income increase indeed indian indiana indians indicate indies indoor industry infantry initial injured injuries injury inline innings inside inspired instance instead integral intended interest interior internal internet invasion invited involved involves iranian ireland islamic island islands isolated israel israeli issued issues italian itself jackson jacques jamaica january japanese jeffrey jenkins jennifer jeremy jersey jessica jewish johann johnny johnson johnston joined joining jonathan jordan joseph joshua journal journey judges judicial julian julien julius junction jungle junior jupiter justice justin kansas keeper keeping kennedy kenneth kentucky kerala keyboard killed killer killing kingdom kingston kitchen knight knights kolonia korean kuwait labels labour ladies landing landmark language largely larger largest lasted latest latino latter latvia launch launched laurent lawrence lawyer layout leader leaders leading league leagues learned learning leaves leaving lebanon legacy legend legends legion length leonard leslie lesser letter letters levels liberal liberty library licence license licensed lifetime lights likely limited limits lincoln linear linked liquid listed listing literacy literary little living locally located location london loneos longer longest looked looking losing losses louise lowest lyrics machine machines madison madrid magazine magical magnetic mainland mainly maintain majority makeup making malaysia malcolm managed manager managers managing manila manitoba manner mansion manual manuel marathon marcus margaret marina marine marines marion maritime marked market markets marriage married marshall martial martin marvel maryland mascot massacre massive master masters matches material matrix matter matters matthew maurice maximum maxwell mcdonald mcmahon meaning measure measures medals median medical medicine medieval medium meeting meetings member members membrane memorial memories memory memphis mental mention mercedes merchant mercury merely merged merger merging mesnil message meters method methods metres mexican mexico michael michel michelle michigan middle midland midlands midnight miguel military miller million milton mineral minimum mining minister ministry minority minute minutes mirror missile missiles missing mission missions missouri mitchell mobile models modern modified moment monday monica monkey monroe monster monsters montana monthly months montreal monument morgan morning morocco morris morrison moscow mosque mostly mother motion motors mountain mounted movement movies moving muhammad multiple munich murder murdered murphy murray museum museums musical musician muslim muslims myspace mystery nacional napoleon narrow nathan nation national nations native natural nature nearby nearest nearly nebraska needed negative neither nelson network networks neutral nevada newman newport newton nicholas nickname nicolas nigeria nights nintendo nominee norfolk normal normally norman northern norton norway notable notably nothing notice novelist novels november nuclear number numbered numbers numerous oakland object objects observed observer obtain obtained occasion occupied occurred occurs october offered offering offers office officer officers offices official oilers oklahoma oldest oldham oliver olympic olympics ongoing online ontario opened opening operate operated operates operator opinion opponent opposed opposite option options orange orbital ordered orders ordinary oregon organic oriental oriented origin original origins orlando orleans orphaned orthodox others ottawa ottoman outdoor output outside overall overseas overview owners oxford pacific package painted painter painting pakistan palace palmer palomar panama papers parade paradise paraguay parallel parent parents parish parker parking partial parties partly partner partners passage passed passes passing patent patient patients patrick patrol pattern patterns peerage penalty people peoples percent perfect perform perhaps period periods persian person personal persons phantom philip phillips phoenix photos phrase phylum physical physics picked picture pictures pieces pierce pierre pilots pioneer pirates pitcher placed places placing plains planet planets planned planning plantae plants plastic plates platform platinum played player players playing playoff playoffs pleasant please plymouth pocket poetry pointed points poland police policies policy polish politics popular porsche portal porter portion portions portland portrait portugal position positive possible possibly postal potter poverty powell powered powerful powers practice pradesh prairie prayer preceded precise premier premiere prepared presence present presents preserve pressure preston prevent previous prices priest primary prince princess printed printing prison prisoner private probably problem problems process produce produced producer produces product products profile profit program programs progress project projects promote promoted proper property proposal proposed protect protein proteins protest protocol proved provide provided provides province prussia public publicly puerto punjab purchase purple purpose purposes qualify quality quarter quartet quebec queens question quickly quoted rabbit rachel racial racing radical rafael railroad railway railways rainbow raised raising randolph random rangers ranges ranging ranked ranking rankings rapidly rapids rarely rather rating ratings raymond reached reaching reaction reader reading reagan reality really reason reasons rebuilt receive received receiver receives recent recently receptor record recorded records recovery reduce reduced referee referred refers reflect reform refuge refugees refused regarded regime regiment region regional regions register regular rejected related relating relation relative release released releases relevant reliable relief religion remain remained remains remember remote remove removed renamed renowned repair repeated replace replaced report reported reporter reports republic request requests require required requires rescue research reserve reserves resident residing resigned resort resource respect response restored result resulted results retail retained retired retreat return returned returns revealed reveals revenge revenue reverse review reviews revised revival rewrite reynolds rhythm richard richards richmond riders riding rights rising rivalry rivers robert roberts robinson rocket rockets rogers roland rolling romance romania romanian romantic ronald rookie roster roughly rounds routes rovers ruling runner runners running russell russia russian sabbath sacred safety sailing sailor sainte saints salvador sample samples samuel santiago santos saturday savage saying scenes schedule scheme scholar scholars school schools science sciences scored scores scoring scotia scotland scottish screen script search season seasons seattle second seconds secret section sections sector secure security seeing seeking seemed segment select selected selling seminary senate senator senators senior sentence separate sequel sequence serbia serbian sergeant serial series serious served server serves service services serving session sessions setting settled settlers seventh several severe sexual shadow shanghai shaped shared shares sharing shepherd sherman shield shipping shooting shopping shortly should showed showing shrine shuttle sidney sierra signal signals signed signing silent silver similar simple simply simpson singer singers singing single singles sister sisters situated skating skills slaves slightly slovakia slovenia slowly smaller smooth soccer social society socorro software soldier soldiers solomon solution someone somerset somewhat sought sounds source sources southern soviet spaces spanish speaker speakers speaking special species specific spectrum speech speedway spencer spider spirit spoken sporting sports spouse spread spring springs squadron square squirrel stable stadium stages standard standing stands stanford stanley starred starring started starting starts stated stateating station stations statue status stayed stephen sterling steven stevens stewart stolen stones stopped storage stores stories straight strange strategy stream street streets strength stress strike striker strikes string strings stroke strong strongly struck struggle stuart student students studied studies studio studios studying styles subject subjects suburb suburban suburbs success suffered suffolk suggest suggests suicide suitable sullivan sultan summary summer summit sunday superior superman supplies supply support supports supposed supreme surface surgery surname surprise surrey survey survive survived sussex sutton suzuki sweden swedish swimming switch sydney symbol symbols symphony syndrome synopsis syracuse system systems tables tactical tagged tailed taiwan taking talent talking tanzania target taught taylor teacher teachers teaching teenage telling temple tennis terminal terminus terror testing thailand thanks theater theatre themes theodore theology theorem theories theory therapy things thinking thirteen thirty thomas thompson thomson though thought thoughts thousand threat throne through thunder thursday ticket tigers timeline titled titles together toledo tomorrow tonight topics toronto torres totals toured touring tourism tourist toward towards towers township tracks traded trading traffic trained trainer training trains transfer transit travel travels treasure treated treaty trials triangle tribes tribune tribute trilogy trinidad trinity triple trivia troops trophy tropical trouble trying tuesday tunnel turkey turkish turned turner turning turnout twelve twenty typhoon typical ukraine ulster ultimate unable unclear uniform unique united universe unknown unless unlike unusual upcoming update updated uruguay useful usually vacant valley valuable values variable variant variants variety various vector vehicle vehicles velocity venice venture venues vermont vernon version versions versus vertical vessel vessels veteran veterans victim victims victor victoria victory videos vienna vietnam viewed village villages villers vincent violence violent violin virgin virginia virtual visible vision visited visiting visitor visitors visits visual vladimir vocalist vocals voiced voices volume volumes voters voting voyage wagner waiting walker walking wallace walter wanted warfare warner warning warren warrior warriors warsaw waters watson wealth weapon weapons wearing weather website webster wedding weekend weekly weight welcome western wheels whereas whether whilst wickets widely wildlife wilhelm william williams willie wilson window windows windsor winner winners winning winnipeg winter wireless within without wizard wonder wooden worked worker workers working worlds worship wounded wrestler wright writer writers writes writing writings written wyoming yankees yellow younger youngest zealand zimbabwe";
			
			// some settings
			$font_file = "./kabob_extrabold_regular_font.ttf";
			$font_size = 45;
			
			// pick a random word
			$words = explode(" ", $wordlist);
			$code = $words[rand(0, count($words)-1)];
			
			// create a random gray shade
			$color = rand(60, 160);
			
			// allocate the image and colors
			$img = imagecreatetruecolor(300, 80);
			$color_bg = imagecolorallocate($img, 255, 255, 255);
			$color_bg_chars = imagecolorallocatealpha($img, $color, $color, $color, 50);
			$color_text_shadow = imagecolorallocatealpha($img, 255, 255, 255, 30);
			$color_text = imagecolorallocatealpha($img, $color, $color, $color, 50);
			
			// clear the background
			imagefilledrectangle($img, 0, 0, 300, 80, $color_bg);
			
			// create the background letters
			$bg_chars = "abcdefghijklmnopqrstuvwxyz";
			for ($i=0; $i<rand(60,120); $i++)
			{
				// randomize the place and angle
				$x = rand(-50, 300);
				$y = rand(-50, 80);
				$angle = rand(-90, 90);
				
				imagettftext($img, $font_size, $angle, $x, $y, $color_bg_chars, $font_file, $bg_chars[rand(0, strlen($bg_chars)-1)]);
			}
			
			// randomize the start of the code
			$x = 50 + rand(-40, 30 - (strlen($code) - 6) * 24);
			$y = 56 + rand(-8, 8);
			
			// write the code letter-by-letter
			for ($i=0; $i<strlen($code); $i++)
			{
				// angle is random
				$angle = rand(-10, 10);
				
				// create the shadow for the letter
				for ($ax=-1; $ax<0; $ax++)
				{
					for ($ay=-1; $ay<0; $ay++)
					{
						imagettftext($img, $font_size, $angle, $x+$ax, $y+$ay, $color_text_shadow, $font_file, $code[$i]);
					}
				}
				
				// create the letter
				imagettftext($img, $font_size, $angle, $x, $y, $color_text, $font_file, $code[$i]);
				
				// calculate the place of the next letter
				$y += rand(-2, 2);
				$tmp = imagettfbbox($font_size, 0, $font_file, $code[$i]);
				$x += $tmp[2]  + rand(-4, 0);
				
			}
			
			// fancy border
			imagerectangle($img, 0, 0, 299, 79, $color_text);
			imagerectangle($img, 1, 1, 298, 78, $color_bg);
			
			// store the code in session
			$_SESSION["captchaz:".$realm] = $code;
			
			// try to avoid caching	
			header("Expires: Mon, 01 Jan 2000 00:00:00 GMT");
			header("Pragma: no-cache");
			header("Cache-Control: no-store, no-cache, must-revalidate, post-check=0, pre-check=0"); 
			
			// put the image
			header("Content-Type: image/png");
			
			// clean up
			imagepng($img);
			imagedestroy($img);
			
			// return the code
			return $code;
		}
		
		static public function Check($code, $realm="captcha")
		{
			// check the supplied code
			$result = array_key_exists("captchaz:".$realm, $_SESSION) && $_SESSION["captchaz:".$realm] == strtolower($code);
			
			// clear the code from session (code cannot be reused/retried)
			unset($_SESSION["captchaz:".$realm]);
			
			// return the result
			return $result;
		}
	}
?>