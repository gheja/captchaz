<?php
	session_start();
	
	require_once("captchaz.class.php");
	
	// check if the user has pressed the submit button
	$posted = array_key_exists("submit", $_POST);
	
	if ($posted)
	{
		$success = Captchaz::Check($_POST['captcha']);
		if ($success)
		{
			// do the stuffs, put into database, etc.
		}
	}
	else
	{
		$posted = false;
	}
?>
<html>
	<head>
		<title>Captchaz test page</title>
	</head>
	<body>
		<h1>Captchaz test page</h1>
		<form action="captchaz_example_form.php" method="post" id="test">
			<p>
				<img src="captchaz_example_image_generator.php" alt="Captcha" /><br/>
				<label for="captcha">The text above:</label>
				<input type="text" class="text" id="captcha" name="captcha" value=""/>
			</p>
			<p>
				<input type="submit" class="submit" name="submit" value="OK" />
			</p>
		</form>
		<?php
			if ($posted)
			{
				if ($success)
				{
					echo "Success.";
				}
				else
				{
					echo "Please try again.";
				}
			}
		?>
	</body>
</html>
