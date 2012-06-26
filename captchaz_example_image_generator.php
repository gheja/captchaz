<?php
	// This is a sample file for generating captcha images.
	session_start();
	
	include("captchaz.class.php");
	
	Captchaz::Generate();
?>