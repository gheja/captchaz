captchaz
========

A PHP based captcha generator.

Requirements
============

Captchaz requires a PHP installation with GD extension and TTF font support.

Some history
============

It was started back in 2008 before reCaptcha and other distributed captcha generators became widely used and there was no real easy-to-use and secure captcha generators for PHP.

The background is not separated from the text in function (ie. it is not a somewhat rotated grid or waves) therefore it is harder to be distinguished by robots but still can fairly easily be read by humans - ad-hoc tests shows that after the first two-three uses it becomes much easier.

It is also not based on stretching, punching, squeezeing the words that can make really hard to be read by humans in some cases - although it might be a good security measures against the robots too (unfortunately).

So it's design principle were simplicity and portability.

Contact
=======

If you have any comments, patches feel free to share them, I'd be more than happy to hear them!
