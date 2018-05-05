function printStackTrace(b){var c=(b&&b.e)?b.e:null;var e=(b&&b.guess)?b.guess:true;var d=new printStackTrace.implementation();var a=d.run(c);return(e)?d.guessFunctions(a):a}printStackTrace.implementation=function(){};printStackTrace.implementation.prototype={run:function(a){var b=this._mode||this.mode();if(b==="other"){return this.other(arguments.callee)}else{a=a||(function(){try{(0)()}catch(c){return c}})();return this[b](a)}},mode:function(){try{(0)()}catch(a){if(a.arguments){return(this._mode="chrome")}else{if(a.stack){return(this._mode="firefox")}else{if(window.opera&&!("stacktrace" in a)){return(this._mode="opera")}}}}return(this._mode="other")},chrome:function(a){return a.stack.replace(/^.*?\n/,"").replace(/^.*?\n/,"").replace(/^.*?\n/,"").replace(/^[^\(]+?[\n$]/gm,"").replace(/^\s+at\s+/gm,"").replace(/^Object.<anonymous>\s*\(/gm,"{anonymous}()@").split("\n")},firefox:function(a){return a.stack.replace(/^.*?\n/,"").replace(/(?:\n@:0)?\s+$/m,"").replace(/^\(/gm,"{anonymous}(").split("\n")},opera:function(h){var c=h.message.split("\n"),b="{anonymous}",g=/Line\s+(\d+).*?script\s+(http\S+)(?:.*?in\s+function\s+(\S+))?/i,f,d,a;for(f=4,d=0,a=c.length;f<a;f+=2){if(g.test(c[f])){c[d++]=(RegExp.$3?RegExp.$3+"()@"+RegExp.$2+RegExp.$1:b+"()@"+RegExp.$2+":"+RegExp.$1)+" -- "+c[f+1].replace(/^\s+/,"")}}c.splice(d,c.length-d);return c},other:function(h){var b="{anonymous}",g=/function\s*([\w\-$]+)?\s*\(/i,a=[],d=0,e,c;var f=10;while(h&&a.length<f){e=g.test(h.toString())?RegExp.$1||b:b;c=Array.prototype.slice.call(h["arguments"]);a[d++]=e+"("+printStackTrace.implementation.prototype.stringifyArguments(c)+")";if(h===h.caller&&window.opera){break}h=h.caller}return a},stringifyArguments:function(a){for(var b=0;b<a.length;++b){var c=a[b];if(typeof c=="object"){a[b]="#object"}else{if(typeof c=="function"){a[b]="#function"}else{if(typeof c=="string"){a[b]='"'+c+'"'}}}}return a.join(",")},sourceCache:{},ajax:function(a){var b=this.createXMLHTTPObject();if(!b){return}b.open("GET",a,false);b.setRequestHeader("User-Agent","XMLHTTP/1.0");b.send("");return b.responseText},createXMLHTTPObject:function(){var c,a=[function(){return new XMLHttpRequest()},function(){return new ActiveXObject("Msxml2.XMLHTTP")},function(){return new ActiveXObject("Msxml3.XMLHTTP")},function(){return new ActiveXObject("Microsoft.XMLHTTP")}];for(var b=0;b<a.length;b++){try{c=a[b]();this.createXMLHTTPObject=a[b];return c}catch(d){}}},getSource:function(a){if(!(a in this.sourceCache)){this.sourceCache[a]=this.ajax(a).split("\n")}return this.sourceCache[a]},guessFunctions:function(b){for(var d=0;d<b.length;++d){var h=/{anonymous}\(.*\)@(\w+:\/\/([-\w\.]+)+(:\d+)?[^:]+):(\d+):?(\d+)?/;var g=b[d],a=h.exec(g);if(a){var c=a[1],f=a[4];if(c&&f){var e=this.guessFunctionName(c,f);b[d]=g.replace("{anonymous}",e)}}}return b},guessFunctionName:function(a,c){try{return this.guessFunctionNameFromLines(c,this.getSource(a))}catch(b){return"getSource failed with url: "+a+", exception: "+b.toString()}},guessFunctionNameFromLines:function(h,f){var c=/function ([^(]*)\(([^)]*)\)/;var g=/['"]?([0-9A-Za-z_]+)['"]?\s*[:=]\s*(function|eval|new Function)/;var b="",d=10;for(var e=0;e<d;++e){b=f[h-e]+b;if(b!==undefined){var a=g.exec(b);if(a){return a[1]}else{a=c.exec(b)}if(a&&a[1]){return a[1]}}}return"(?)"}};
!function(t,e,i){var n=t.L,o={};o.version="0.7.3","object"==typeof module&&"object"==typeof module.exports?module.exports=o:"function"==typeof define&&define.amd&&define(o),o.noConflict=function(){return t.L=n,this},t.L=o,o.Util={extend:function(t){var e,i,n,o,s=Array.prototype.slice.call(arguments,1);for(i=0,n=s.length;n>i;i++){o=s[i]||{};for(e in o)o.hasOwnProperty(e)&&(t[e]=o[e])}return t},bind:function(t,e){var i=arguments.length>2?Array.prototype.slice.call(arguments,2):null;return function(){return t.apply(e,i||arguments)}},stamp:function(){var t=0,e="_leaflet_id";return function(i){return i[e]=i[e]||++t,i[e]}}(),invokeEach:function(t,e,i){var n,o;if("object"==typeof t){o=Array.prototype.slice.call(arguments,3);for(n in t)e.apply(i,[n,t[n]].concat(o));return!0}return!1},limitExecByInterval:function(t,e,i){var n,o;return function s(){var a=arguments;return n?void(o=!0):(n=!0,setTimeout(function(){n=!1,o&&(s.apply(i,a),o=!1)},e),void t.apply(i,a))}},falseFn:function(){return!1},formatNum:function(t,e){var i=Math.pow(10,e||5);return Math.round(t*i)/i},trim:function(t){return t.trim?t.trim():t.replace(/^\s+|\s+$/g,"")},splitWords:function(t){return o.Util.trim(t).split(/\s+/)},setOptions:function(t,e){return t.options=o.extend({},t.options,e),t.options},getParamString:function(t,e,i){var n=[];for(var o in t)n.push(encodeURIComponent(i?o.toUpperCase():o)+"="+encodeURIComponent(t[o]));return(e&&-1!==e.indexOf("?")?"&":"?")+n.join("&")},template:function(t,e){return t.replace(/\{ *([\w_]+) *\}/g,function(t,n){var o=e[n];if(o===i)throw new Error("No value provided for variable "+t);return"function"==typeof o&&(o=o(e)),o})},isArray:Array.isArray||function(t){return"[object Array]"===Object.prototype.toString.call(t)},emptyImageUrl:"data:image/gif;base64,R0lGODlhAQABAAD/ACwAAAAAAQABAAACADs="},function(){function e(e){var i,n,o=["webkit","moz","o","ms"];for(i=0;i<o.length&&!n;i++)n=t[o[i]+e];return n}function i(e){var i=+new Date,o=Math.max(0,16-(i-n));return n=i+o,t.setTimeout(e,o)}var n=0,s=t.requestAnimationFrame||e("RequestAnimationFrame")||i,a=t.cancelAnimationFrame||e("CancelAnimationFrame")||e("CancelRequestAnimationFrame")||function(e){t.clearTimeout(e)};o.Util.requestAnimFrame=function(e,n,a,r){return e=o.bind(e,n),a&&s===i?void e():s.call(t,e,r)},o.Util.cancelAnimFrame=function(e){e&&a.call(t,e)}}(),o.extend=o.Util.extend,o.bind=o.Util.bind,o.stamp=o.Util.stamp,o.setOptions=o.Util.setOptions,o.Class=function(){},o.Class.extend=function(t){var e=function(){this.initialize&&this.initialize.apply(this,arguments),this._initHooks&&this.callInitHooks()},i=function(){};i.prototype=this.prototype;var n=new i;n.constructor=e,e.prototype=n;for(var s in this)this.hasOwnProperty(s)&&"prototype"!==s&&(e[s]=this[s]);t.statics&&(o.extend(e,t.statics),delete t.statics),t.includes&&(o.Util.extend.apply(null,[n].concat(t.includes)),delete t.includes),t.options&&n.options&&(t.options=o.extend({},n.options,t.options)),o.extend(n,t),n._initHooks=[];var a=this;return e.__super__=a.prototype,n.callInitHooks=function(){if(!this._initHooksCalled){a.prototype.callInitHooks&&a.prototype.callInitHooks.call(this),this._initHooksCalled=!0;for(var t=0,e=n._initHooks.length;e>t;t++)n._initHooks[t].call(this)}},e},o.Class.include=function(t){o.extend(this.prototype,t)},o.Class.mergeOptions=function(t){o.extend(this.prototype.options,t)},o.Class.addInitHook=function(t){var e=Array.prototype.slice.call(arguments,1),i="function"==typeof t?t:function(){this[t].apply(this,e)};this.prototype._initHooks=this.prototype._initHooks||[],this.prototype._initHooks.push(i)};var s="_leaflet_events";o.Mixin={},o.Mixin.Events={addEventListener:function(t,e,i){if(o.Util.invokeEach(t,this.addEventListener,this,e,i))return this;var n,a,r,h,l,u,c,d=this[s]=this[s]||{},p=i&&i!==this&&o.stamp(i);for(t=o.Util.splitWords(t),n=0,a=t.length;a>n;n++)r={action:e,context:i||this},h=t[n],p?(l=h+"_idx",u=l+"_len",c=d[l]=d[l]||{},c[p]||(c[p]=[],d[u]=(d[u]||0)+1),c[p].push(r)):(d[h]=d[h]||[],d[h].push(r));return this},hasEventListeners:function(t){var e=this[s];return!!e&&(t in e&&e[t].length>0||t+"_idx"in e&&e[t+"_idx_len"]>0)},removeEventListener:function(t,e,i){if(!this[s])return this;if(!t)return this.clearAllEventListeners();if(o.Util.invokeEach(t,this.removeEventListener,this,e,i))return this;var n,a,r,h,l,u,c,d,p,_=this[s],m=i&&i!==this&&o.stamp(i);for(t=o.Util.splitWords(t),n=0,a=t.length;a>n;n++)if(r=t[n],u=r+"_idx",c=u+"_len",d=_[u],e){if(h=m&&d?d[m]:_[r]){for(l=h.length-1;l>=0;l--)h[l].action!==e||i&&h[l].context!==i||(p=h.splice(l,1),p[0].action=o.Util.falseFn);i&&d&&0===h.length&&(delete d[m],_[c]--)}}else delete _[r],delete _[u],delete _[c];return this},clearAllEventListeners:function(){return delete this[s],this},fireEvent:function(t,e){if(!this.hasEventListeners(t))return this;var i,n,a,r,h,l=o.Util.extend({},e,{type:t,target:this}),u=this[s];if(u[t])for(i=u[t].slice(),n=0,a=i.length;a>n;n++)i[n].action.call(i[n].context,l);r=u[t+"_idx"];for(h in r)if(i=r[h].slice())for(n=0,a=i.length;a>n;n++)i[n].action.call(i[n].context,l);return this},addOneTimeEventListener:function(t,e,i){if(o.Util.invokeEach(t,this.addOneTimeEventListener,this,e,i))return this;var n=o.bind(function(){this.removeEventListener(t,e,i).removeEventListener(t,n,i)},this);return this.addEventListener(t,e,i).addEventListener(t,n,i)}},o.Mixin.Events.on=o.Mixin.Events.addEventListener,o.Mixin.Events.off=o.Mixin.Events.removeEventListener,o.Mixin.Events.once=o.Mixin.Events.addOneTimeEventListener,o.Mixin.Events.fire=o.Mixin.Events.fireEvent,function(){var n="ActiveXObject"in t,s=n&&!e.addEventListener,a=navigator.userAgent.toLowerCase(),r=-1!==a.indexOf("webkit"),h=-1!==a.indexOf("chrome"),l=-1!==a.indexOf("phantom"),u=-1!==a.indexOf("android"),c=-1!==a.search("android [23]"),d=-1!==a.indexOf("gecko"),p=typeof orientation!=i+"",_=t.navigator&&t.navigator.msPointerEnabled&&t.navigator.msMaxTouchPoints&&!t.PointerEvent,m=t.PointerEvent&&t.navigator.pointerEnabled&&t.navigator.maxTouchPoints||_,f="devicePixelRatio"in t&&t.devicePixelRatio>1||"matchMedia"in t&&t.matchMedia("(min-resolution:144dpi)")&&t.matchMedia("(min-resolution:144dpi)").matches,g=e.documentElement,v=n&&"transition"in g.style,y="WebKitCSSMatrix"in t&&"m11"in new t.WebKitCSSMatrix&&!c,P="MozPerspective"in g.style,L="OTransition"in g.style,x=!t.L_DISABLE_3D&&(v||y||P||L)&&!l,w=!t.L_NO_TOUCH&&!l&&function(){var t="ontouchstart";if(m||t in g)return!0;var i=e.createElement("div"),n=!1;return i.setAttribute?(i.setAttribute(t,"return;"),"function"==typeof i[t]&&(n=!0),i.removeAttribute(t),i=null,n):!1}();o.Browser={ie:n,ielt9:s,webkit:r,gecko:d&&!r&&!t.opera&&!n,android:u,android23:c,chrome:h,ie3d:v,webkit3d:y,gecko3d:P,opera3d:L,any3d:x,mobile:p,mobileWebkit:p&&r,mobileWebkit3d:p&&y,mobileOpera:p&&t.opera,touch:w,msPointer:_,pointer:m,retina:f}}(),o.Point=function(t,e,i){this.x=i?Math.round(t):t,this.y=i?Math.round(e):e},o.Point.prototype={clone:function(){return new o.Point(this.x,this.y)},add:function(t){return this.clone()._add(o.point(t))},_add:function(t){return this.x+=t.x,this.y+=t.y,this},subtract:function(t){return this.clone()._subtract(o.point(t))},_subtract:function(t){return this.x-=t.x,this.y-=t.y,this},divideBy:function(t){return this.clone()._divideBy(t)},_divideBy:function(t){return this.x/=t,this.y/=t,this},multiplyBy:function(t){return this.clone()._multiplyBy(t)},_multiplyBy:function(t){return this.x*=t,this.y*=t,this},round:function(){return this.clone()._round()},_round:function(){return this.x=Math.round(this.x),this.y=Math.round(this.y),this},floor:function(){return this.clone()._floor()},_floor:function(){return this.x=Math.floor(this.x),this.y=Math.floor(this.y),this},distanceTo:function(t){t=o.point(t);var e=t.x-this.x,i=t.y-this.y;return Math.sqrt(e*e+i*i)},equals:function(t){return t=o.point(t),t.x===this.x&&t.y===this.y},contains:function(t){return t=o.point(t),Math.abs(t.x)<=Math.abs(this.x)&&Math.abs(t.y)<=Math.abs(this.y)},toString:function(){return"Point("+o.Util.formatNum(this.x)+", "+o.Util.formatNum(this.y)+")"}},o.point=function(t,e,n){return t instanceof o.Point?t:o.Util.isArray(t)?new o.Point(t[0],t[1]):t===i||null===t?t:new o.Point(t,e,n)},o.Bounds=function(t,e){if(t)for(var i=e?[t,e]:t,n=0,o=i.length;o>n;n++)this.extend(i[n])},o.Bounds.prototype={extend:function(t){return t=o.point(t),this.min||this.max?(this.min.x=Math.min(t.x,this.min.x),this.max.x=Math.max(t.x,this.max.x),this.min.y=Math.min(t.y,this.min.y),this.max.y=Math.max(t.y,this.max.y)):(this.min=t.clone(),this.max=t.clone()),this},getCenter:function(t){return new o.Point((this.min.x+this.max.x)/2,(this.min.y+this.max.y)/2,t)},getBottomLeft:function(){return new o.Point(this.min.x,this.max.y)},getTopRight:function(){return new o.Point(this.max.x,this.min.y)},getSize:function(){return this.max.subtract(this.min)},contains:function(t){var e,i;return t="number"==typeof t[0]||t instanceof o.Point?o.point(t):o.bounds(t),t instanceof o.Bounds?(e=t.min,i=t.max):e=i=t,e.x>=this.min.x&&i.x<=this.max.x&&e.y>=this.min.y&&i.y<=this.max.y},intersects:function(t){t=o.bounds(t);var e=this.min,i=this.max,n=t.min,s=t.max,a=s.x>=e.x&&n.x<=i.x,r=s.y>=e.y&&n.y<=i.y;return a&&r},isValid:function(){return!(!this.min||!this.max)}},o.bounds=function(t,e){return!t||t instanceof o.Bounds?t:new o.Bounds(t,e)},o.Transformation=function(t,e,i,n){this._a=t,this._b=e,this._c=i,this._d=n},o.Transformation.prototype={transform:function(t,e){return this._transform(t.clone(),e)},_transform:function(t,e){return e=e||1,t.x=e*(this._a*t.x+this._b),t.y=e*(this._c*t.y+this._d),t},untransform:function(t,e){return e=e||1,new o.Point((t.x/e-this._b)/this._a,(t.y/e-this._d)/this._c)}},o.DomUtil={get:function(t){return"string"==typeof t?e.getElementById(t):t},getStyle:function(t,i){var n=t.style[i];if(!n&&t.currentStyle&&(n=t.currentStyle[i]),(!n||"auto"===n)&&e.defaultView){var o=e.defaultView.getComputedStyle(t,null);n=o?o[i]:null}return"auto"===n?null:n},getViewportOffset:function(t){var i,n=0,s=0,a=t,r=e.body,h=e.documentElement;do{if(n+=a.offsetTop||0,s+=a.offsetLeft||0,n+=parseInt(o.DomUtil.getStyle(a,"borderTopWidth"),10)||0,s+=parseInt(o.DomUtil.getStyle(a,"borderLeftWidth"),10)||0,i=o.DomUtil.getStyle(a,"position"),a.offsetParent===r&&"absolute"===i)break;if("fixed"===i){n+=r.scrollTop||h.scrollTop||0,s+=r.scrollLeft||h.scrollLeft||0;break}if("relative"===i&&!a.offsetLeft){var l=o.DomUtil.getStyle(a,"width"),u=o.DomUtil.getStyle(a,"max-width"),c=a.getBoundingClientRect();("none"!==l||"none"!==u)&&(s+=c.left+a.clientLeft),n+=c.top+(r.scrollTop||h.scrollTop||0);break}a=a.offsetParent}while(a);a=t;do{if(a===r)break;n-=a.scrollTop||0,s-=a.scrollLeft||0,a=a.parentNode}while(a);return new o.Point(s,n)},documentIsLtr:function(){return o.DomUtil._docIsLtrCached||(o.DomUtil._docIsLtrCached=!0,o.DomUtil._docIsLtr="ltr"===o.DomUtil.getStyle(e.body,"direction")),o.DomUtil._docIsLtr},create:function(t,i,n){var o=e.createElement(t);return o.className=i,n&&n.appendChild(o),o},hasClass:function(t,e){if(t.classList!==i)return t.classList.contains(e);var n=o.DomUtil._getClass(t);return n.length>0&&new RegExp("(^|\\s)"+e+"(\\s|$)").test(n)},addClass:function(t,e){if(t.classList!==i)for(var n=o.Util.splitWords(e),s=0,a=n.length;a>s;s++)t.classList.add(n[s]);else if(!o.DomUtil.hasClass(t,e)){var r=o.DomUtil._getClass(t);o.DomUtil._setClass(t,(r?r+" ":"")+e)}},removeClass:function(t,e){t.classList!==i?t.classList.remove(e):o.DomUtil._setClass(t,o.Util.trim((" "+o.DomUtil._getClass(t)+" ").replace(" "+e+" "," ")))},_setClass:function(t,e){t.className.baseVal===i?t.className=e:t.className.baseVal=e},_getClass:function(t){return t.className.baseVal===i?t.className:t.className.baseVal},setOpacity:function(t,e){if("opacity"in t.style)t.style.opacity=e;else if("filter"in t.style){var i=!1,n="DXImageTransform.Microsoft.Alpha";try{i=t.filters.item(n)}catch(o){if(1===e)return}e=Math.round(100*e),i?(i.Enabled=100!==e,i.Opacity=e):t.style.filter+=" progid:"+n+"(opacity="+e+")"}},testProp:function(t){for(var i=e.documentElement.style,n=0;n<t.length;n++)if(t[n]in i)return t[n];return!1},getTranslateString:function(t){var e=o.Browser.webkit3d,i="translate"+(e?"3d":"")+"(",n=(e?",0":"")+")";return i+t.x+"px,"+t.y+"px"+n},getScaleString:function(t,e){var i=o.DomUtil.getTranslateString(e.add(e.multiplyBy(-1*t))),n=" scale("+t+") ";return i+n},setPosition:function(t,e,i){t._leaflet_pos=e,!i&&o.Browser.any3d?t.style[o.DomUtil.TRANSFORM]=o.DomUtil.getTranslateString(e):(t.style.left=e.x+"px",t.style.top=e.y+"px")},getPosition:function(t){return t._leaflet_pos}},o.DomUtil.TRANSFORM=o.DomUtil.testProp(["transform","WebkitTransform","OTransform","MozTransform","msTransform"]),o.DomUtil.TRANSITION=o.DomUtil.testProp(["webkitTransition","transition","OTransition","MozTransition","msTransition"]),o.DomUtil.TRANSITION_END="webkitTransition"===o.DomUtil.TRANSITION||"OTransition"===o.DomUtil.TRANSITION?o.DomUtil.TRANSITION+"End":"transitionend",function(){if("onselectstart"in e)o.extend(o.DomUtil,{disableTextSelection:function(){o.DomEvent.on(t,"selectstart",o.DomEvent.preventDefault)},enableTextSelection:function(){o.DomEvent.off(t,"selectstart",o.DomEvent.preventDefault)}});else{var i=o.DomUtil.testProp(["userSelect","WebkitUserSelect","OUserSelect","MozUserSelect","msUserSelect"]);o.extend(o.DomUtil,{disableTextSelection:function(){if(i){var t=e.documentElement.style;this._userSelect=t[i],t[i]="none"}},enableTextSelection:function(){i&&(e.documentElement.style[i]=this._userSelect,delete this._userSelect)}})}o.extend(o.DomUtil,{disableImageDrag:function(){o.DomEvent.on(t,"dragstart",o.DomEvent.preventDefault)},enableImageDrag:function(){o.DomEvent.off(t,"dragstart",o.DomEvent.preventDefault)}})}(),o.LatLng=function(t,e,n){if(t=parseFloat(t),e=parseFloat(e),isNaN(t)||isNaN(e))throw new Error("Invalid LatLng object: ("+t+", "+e+")");this.lat=t,this.lng=e,n!==i&&(this.alt=parseFloat(n))},o.extend(o.LatLng,{DEG_TO_RAD:Math.PI/180,RAD_TO_DEG:180/Math.PI,MAX_MARGIN:1e-9}),o.LatLng.prototype={equals:function(t){if(!t)return!1;t=o.latLng(t);var e=Math.max(Math.abs(this.lat-t.lat),Math.abs(this.lng-t.lng));return e<=o.LatLng.MAX_MARGIN},toString:function(t){return"LatLng("+o.Util.formatNum(this.lat,t)+", "+o.Util.formatNum(this.lng,t)+")"},distanceTo:function(t){t=o.latLng(t);var e=6378137,i=o.LatLng.DEG_TO_RAD,n=(t.lat-this.lat)*i,s=(t.lng-this.lng)*i,a=this.lat*i,r=t.lat*i,h=Math.sin(n/2),l=Math.sin(s/2),u=h*h+l*l*Math.cos(a)*Math.cos(r);return 2*e*Math.atan2(Math.sqrt(u),Math.sqrt(1-u))},wrap:function(t,e){var i=this.lng;return t=t||-180,e=e||180,i=(i+e)%(e-t)+(t>i||i===e?e:t),new o.LatLng(this.lat,i)}},o.latLng=function(t,e){return t instanceof o.LatLng?t:o.Util.isArray(t)?"number"==typeof t[0]||"string"==typeof t[0]?new o.LatLng(t[0],t[1],t[2]):null:t===i||null===t?t:"object"==typeof t&&"lat"in t?new o.LatLng(t.lat,"lng"in t?t.lng:t.lon):e===i?null:new o.LatLng(t,e)},o.LatLngBounds=function(t,e){if(t)for(var i=e?[t,e]:t,n=0,o=i.length;o>n;n++)this.extend(i[n])},o.LatLngBounds.prototype={extend:function(t){if(!t)return this;var e=o.latLng(t);return t=null!==e?e:o.latLngBounds(t),t instanceof o.LatLng?this._southWest||this._northEast?(this._southWest.lat=Math.min(t.lat,this._southWest.lat),this._southWest.lng=Math.min(t.lng,this._southWest.lng),this._northEast.lat=Math.max(t.lat,this._northEast.lat),this._northEast.lng=Math.max(t.lng,this._northEast.lng)):(this._southWest=new o.LatLng(t.lat,t.lng),this._northEast=new o.LatLng(t.lat,t.lng)):t instanceof o.LatLngBounds&&(this.extend(t._southWest),this.extend(t._northEast)),this},pad:function(t){var e=this._southWest,i=this._northEast,n=Math.abs(e.lat-i.lat)*t,s=Math.abs(e.lng-i.lng)*t;return new o.LatLngBounds(new o.LatLng(e.lat-n,e.lng-s),new o.LatLng(i.lat+n,i.lng+s))},getCenter:function(){return new o.LatLng((this._southWest.lat+this._northEast.lat)/2,(this._southWest.lng+this._northEast.lng)/2)},getSouthWest:function(){return this._southWest},getNorthEast:function(){return this._northEast},getNorthWest:function(){return new o.LatLng(this.getNorth(),this.getWest())},getSouthEast:function(){return new o.LatLng(this.getSouth(),this.getEast())},getWest:function(){return this._southWest.lng},getSouth:function(){return this._southWest.lat},getEast:function(){return this._northEast.lng},getNorth:function(){return this._northEast.lat},contains:function(t){t="number"==typeof t[0]||t instanceof o.LatLng?o.latLng(t):o.latLngBounds(t);var e,i,n=this._southWest,s=this._northEast;return t instanceof o.LatLngBounds?(e=t.getSouthWest(),i=t.getNorthEast()):e=i=t,e.lat>=n.lat&&i.lat<=s.lat&&e.lng>=n.lng&&i.lng<=s.lng},intersects:function(t){t=o.latLngBounds(t);var e=this._southWest,i=this._northEast,n=t.getSouthWest(),s=t.getNorthEast(),a=s.lat>=e.lat&&n.lat<=i.lat,r=s.lng>=e.lng&&n.lng<=i.lng;return a&&r},toBBoxString:function(){return[this.getWest(),this.getSouth(),this.getEast(),this.getNorth()].join(",")},equals:function(t){return t?(t=o.latLngBounds(t),this._southWest.equals(t.getSouthWest())&&this._northEast.equals(t.getNorthEast())):!1},isValid:function(){return!(!this._southWest||!this._northEast)}},o.latLngBounds=function(t,e){return!t||t instanceof o.LatLngBounds?t:new o.LatLngBounds(t,e)},o.Projection={},o.Projection.SphericalMercator={MAX_LATITUDE:85.0511287798,project:function(t){var e=o.LatLng.DEG_TO_RAD,i=this.MAX_LATITUDE,n=Math.max(Math.min(i,t.lat),-i),s=t.lng*e,a=n*e;return a=Math.log(Math.tan(Math.PI/4+a/2)),new o.Point(s,a)},unproject:function(t){var e=o.LatLng.RAD_TO_DEG,i=t.x*e,n=(2*Math.atan(Math.exp(t.y))-Math.PI/2)*e;return new o.LatLng(n,i)}},o.Projection.LonLat={project:function(t){return new o.Point(t.lng,t.lat)},unproject:function(t){return new o.LatLng(t.y,t.x)}},o.CRS={latLngToPoint:function(t,e){var i=this.projection.project(t),n=this.scale(e);return this.transformation._transform(i,n)},pointToLatLng:function(t,e){var i=this.scale(e),n=this.transformation.untransform(t,i);return this.projection.unproject(n)},project:function(t){return this.projection.project(t)},scale:function(t){return 256*Math.pow(2,t)},getSize:function(t){var e=this.scale(t);return o.point(e,e)}},o.CRS.Simple=o.extend({},o.CRS,{projection:o.Projection.LonLat,transformation:new o.Transformation(1,0,-1,0),scale:function(t){return Math.pow(2,t)}}),o.CRS.EPSG3857=o.extend({},o.CRS,{code:"EPSG:3857",projection:o.Projection.SphericalMercator,transformation:new o.Transformation(.5/Math.PI,.5,-.5/Math.PI,.5),project:function(t){var e=this.projection.project(t),i=6378137;return e.multiplyBy(i)}}),o.CRS.EPSG900913=o.extend({},o.CRS.EPSG3857,{code:"EPSG:900913"}),o.CRS.EPSG4326=o.extend({},o.CRS,{code:"EPSG:4326",projection:o.Projection.LonLat,transformation:new o.Transformation(1/360,.5,-1/360,.5)}),o.Map=o.Class.extend({includes:o.Mixin.Events,options:{crs:o.CRS.EPSG3857,fadeAnimation:o.DomUtil.TRANSITION&&!o.Browser.android23,trackResize:!0,markerZoomAnimation:o.DomUtil.TRANSITION&&o.Browser.any3d},initialize:function(t,e){e=o.setOptions(this,e),this._initContainer(t),this._initLayout(),this._onResize=o.bind(this._onResize,this),this._initEvents(),e.maxBounds&&this.setMaxBounds(e.maxBounds),e.center&&e.zoom!==i&&this.setView(o.latLng(e.center),e.zoom,{reset:!0}),this._handlers=[],this._layers={},this._zoomBoundLayers={},this._tileLayersNum=0,this.callInitHooks(),this._addLayers(e.layers)},setView:function(t,e){return e=e===i?this.getZoom():e,this._resetView(o.latLng(t),this._limitZoom(e)),this},setZoom:function(t,e){return this._loaded?this.setView(this.getCenter(),t,{zoom:e}):(this._zoom=this._limitZoom(t),this)},zoomIn:function(t,e){return this.setZoom(this._zoom+(t||1),e)},zoomOut:function(t,e){return this.setZoom(this._zoom-(t||1),e)},setZoomAround:function(t,e,i){var n=this.getZoomScale(e),s=this.getSize().divideBy(2),a=t instanceof o.Point?t:this.latLngToContainerPoint(t),r=a.subtract(s).multiplyBy(1-1/n),h=this.containerPointToLatLng(s.add(r));return this.setView(h,e,{zoom:i})},fitBounds:function(t,e){e=e||{},t=t.getBounds?t.getBounds():o.latLngBounds(t);var i=o.point(e.paddingTopLeft||e.padding||[0,0]),n=o.point(e.paddingBottomRight||e.padding||[0,0]),s=this.getBoundsZoom(t,!1,i.add(n)),a=n.subtract(i).divideBy(2),r=this.project(t.getSouthWest(),s),h=this.project(t.getNorthEast(),s),l=this.unproject(r.add(h).divideBy(2).add(a),s);return s=e&&e.maxZoom?Math.min(e.maxZoom,s):s,this.setView(l,s,e)},fitWorld:function(t){return this.fitBounds([[-90,-180],[90,180]],t)},panTo:function(t,e){return this.setView(t,this._zoom,{pan:e})},panBy:function(t){return this.fire("movestart"),this._rawPanBy(o.point(t)),this.fire("move"),this.fire("moveend")},setMaxBounds:function(t){return t=o.latLngBounds(t),this.options.maxBounds=t,t?(this._loaded&&this._panInsideMaxBounds(),this.on("moveend",this._panInsideMaxBounds,this)):this.off("moveend",this._panInsideMaxBounds,this)},panInsideBounds:function(t,e){var i=this.getCenter(),n=this._limitCenter(i,this._zoom,t);return i.equals(n)?this:this.panTo(n,e)},addLayer:function(t){var e=o.stamp(t);return this._layers[e]?this:(this._layers[e]=t,!t.options||isNaN(t.options.maxZoom)&&isNaN(t.options.minZoom)||(this._zoomBoundLayers[e]=t,this._updateZoomLevels()),this.options.zoomAnimation&&o.TileLayer&&t instanceof o.TileLayer&&(this._tileLayersNum++,this._tileLayersToLoad++,t.on("load",this._onTileLayerLoad,this)),this._loaded&&this._layerAdd(t),this)},removeLayer:function(t){var e=o.stamp(t);return this._layers[e]?(this._loaded&&t.onRemove(this),delete this._layers[e],this._loaded&&this.fire("layerremove",{layer:t}),this._zoomBoundLayers[e]&&(delete this._zoomBoundLayers[e],this._updateZoomLevels()),this.options.zoomAnimation&&o.TileLayer&&t instanceof o.TileLayer&&(this._tileLayersNum--,this._tileLayersToLoad--,t.off("load",this._onTileLayerLoad,this)),this):this},hasLayer:function(t){return t?o.stamp(t)in this._layers:!1},eachLayer:function(t,e){for(var i in this._layers)t.call(e,this._layers[i]);return this},invalidateSize:function(t){if(!this._loaded)return this;t=o.extend({animate:!1,pan:!0},t===!0?{animate:!0}:t);var e=this.getSize();this._sizeChanged=!0,this._initialCenter=null;var i=this.getSize(),n=e.divideBy(2).round(),s=i.divideBy(2).round(),a=n.subtract(s);return a.x||a.y?(t.animate&&t.pan?this.panBy(a):(t.pan&&this._rawPanBy(a),this.fire("move"),t.debounceMoveend?(clearTimeout(this._sizeTimer),this._sizeTimer=setTimeout(o.bind(this.fire,this,"moveend"),200)):this.fire("moveend")),this.fire("resize",{oldSize:e,newSize:i})):this},addHandler:function(t,e){if(!e)return this;var i=this[t]=new e(this);return this._handlers.push(i),this.options[t]&&i.enable(),this},remove:function(){this._loaded&&this.fire("unload"),this._initEvents("off");try{delete this._container._leaflet}catch(t){this._container._leaflet=i}return this._clearPanes(),this._clearControlPos&&this._clearControlPos(),this._clearHandlers(),this},getCenter:function(){return this._checkIfLoaded(),this._initialCenter&&!this._moved()?this._initialCenter:this.layerPointToLatLng(this._getCenterLayerPoint())},getZoom:function(){return this._zoom},getBounds:function(){var t=this.getPixelBounds(),e=this.unproject(t.getBottomLeft()),i=this.unproject(t.getTopRight());return new o.LatLngBounds(e,i)},getMinZoom:function(){return this.options.minZoom===i?this._layersMinZoom===i?0:this._layersMinZoom:this.options.minZoom},getMaxZoom:function(){return this.options.maxZoom===i?this._layersMaxZoom===i?1/0:this._layersMaxZoom:this.options.maxZoom},getBoundsZoom:function(t,e,i){t=o.latLngBounds(t);var n,s=this.getMinZoom()-(e?1:0),a=this.getMaxZoom(),r=this.getSize(),h=t.getNorthWest(),l=t.getSouthEast(),u=!0;i=o.point(i||[0,0]);do s++,n=this.project(l,s).subtract(this.project(h,s)).add(i),u=e?n.x<r.x||n.y<r.y:r.contains(n);while(u&&a>=s);return u&&e?null:e?s:s-1},getSize:function(){return(!this._size||this._sizeChanged)&&(this._size=new o.Point(this._container.clientWidth,this._container.clientHeight),this._sizeChanged=!1),this._size.clone()},getPixelBounds:function(){var t=this._getTopLeftPoint();return new o.Bounds(t,t.add(this.getSize()))},getPixelOrigin:function(){return this._checkIfLoaded(),this._initialTopLeftPoint},getPanes:function(){return this._panes},getContainer:function(){return this._container},getZoomScale:function(t){var e=this.options.crs;return e.scale(t)/e.scale(this._zoom)},getScaleZoom:function(t){return this._zoom+Math.log(t)/Math.LN2},project:function(t,e){return e=e===i?this._zoom:e,this.options.crs.latLngToPoint(o.latLng(t),e)},unproject:function(t,e){return e=e===i?this._zoom:e,this.options.crs.pointToLatLng(o.point(t),e)},layerPointToLatLng:function(t){var e=o.point(t).add(this.getPixelOrigin());return this.unproject(e)},latLngToLayerPoint:function(t){var e=this.project(o.latLng(t))._round();return e._subtract(this.getPixelOrigin())},containerPointToLayerPoint:function(t){return o.point(t).subtract(this._getMapPanePos())},layerPointToContainerPoint:function(t){return o.point(t).add(this._getMapPanePos())},containerPointToLatLng:function(t){var e=this.containerPointToLayerPoint(o.point(t));return this.layerPointToLatLng(e)},latLngToContainerPoint:function(t){return this.layerPointToContainerPoint(this.latLngToLayerPoint(o.latLng(t)))},mouseEventToContainerPoint:function(t){return o.DomEvent.getMousePosition(t,this._container)},mouseEventToLayerPoint:function(t){return this.containerPointToLayerPoint(this.mouseEventToContainerPoint(t))},mouseEventToLatLng:function(t){return this.layerPointToLatLng(this.mouseEventToLayerPoint(t))},_initContainer:function(t){var e=this._container=o.DomUtil.get(t);if(!e)throw new Error("Map container not found.");if(e._leaflet)throw new Error("Map container is already initialized.");e._leaflet=!0},_initLayout:function(){var t=this._container;o.DomUtil.addClass(t,"leaflet-container"+(o.Browser.touch?" leaflet-touch":"")+(o.Browser.retina?" leaflet-retina":"")+(o.Browser.ielt9?" leaflet-oldie":"")+(this.options.fadeAnimation?" leaflet-fade-anim":""));var e=o.DomUtil.getStyle(t,"position");"absolute"!==e&&"relative"!==e&&"fixed"!==e&&(t.style.position="relative"),this._initPanes(),this._initControlPos&&this._initControlPos()},_initPanes:function(){var t=this._panes={};this._mapPane=t.mapPane=this._createPane("leaflet-map-pane",this._container),this._tilePane=t.tilePane=this._createPane("leaflet-tile-pane",this._mapPane),t.objectsPane=this._createPane("leaflet-objects-pane",this._mapPane),t.shadowPane=this._createPane("leaflet-shadow-pane"),t.overlayPane=this._createPane("leaflet-overlay-pane"),t.markerPane=this._createPane("leaflet-marker-pane"),t.popupPane=this._createPane("leaflet-popup-pane");var e=" leaflet-zoom-hide";this.options.markerZoomAnimation||(o.DomUtil.addClass(t.markerPane,e),o.DomUtil.addClass(t.shadowPane,e),o.DomUtil.addClass(t.popupPane,e))},_createPane:function(t,e){return o.DomUtil.create("div",t,e||this._panes.objectsPane)},_clearPanes:function(){this._container.removeChild(this._mapPane)},_addLayers:function(t){t=t?o.Util.isArray(t)?t:[t]:[];for(var e=0,i=t.length;i>e;e++)this.addLayer(t[e])},_resetView:function(t,e,i,n){var s=this._zoom!==e;n||(this.fire("movestart"),s&&this.fire("zoomstart")),this._zoom=e,this._initialCenter=t,this._initialTopLeftPoint=this._getNewTopLeftPoint(t),i?this._initialTopLeftPoint._add(this._getMapPanePos()):o.DomUtil.setPosition(this._mapPane,new o.Point(0,0)),this._tileLayersToLoad=this._tileLayersNum;var a=!this._loaded;this._loaded=!0,this.fire("viewreset",{hard:!i}),a&&(this.fire("load"),this.eachLayer(this._layerAdd,this)),this.fire("move"),(s||n)&&this.fire("zoomend"),this.fire("moveend",{hard:!i})},_rawPanBy:function(t){o.DomUtil.setPosition(this._mapPane,this._getMapPanePos().subtract(t))},_getZoomSpan:function(){return this.getMaxZoom()-this.getMinZoom()},_updateZoomLevels:function(){var t,e=1/0,n=-1/0,o=this._getZoomSpan();for(t in this._zoomBoundLayers){var s=this._zoomBoundLayers[t];isNaN(s.options.minZoom)||(e=Math.min(e,s.options.minZoom)),isNaN(s.options.maxZoom)||(n=Math.max(n,s.options.maxZoom))}t===i?this._layersMaxZoom=this._layersMinZoom=i:(this._layersMaxZoom=n,this._layersMinZoom=e),o!==this._getZoomSpan()&&this.fire("zoomlevelschange")},_panInsideMaxBounds:function(){this.panInsideBounds(this.options.maxBounds)},_checkIfLoaded:function(){if(!this._loaded)throw new Error("Set map center and zoom first.")},_initEvents:function(e){if(o.DomEvent){e=e||"on",o.DomEvent[e](this._container,"click",this._onMouseClick,this);var i,n,s=["dblclick","mousedown","mouseup","mouseenter","mouseleave","mousemove","contextmenu"];for(i=0,n=s.length;n>i;i++)o.DomEvent[e](this._container,s[i],this._fireMouseEvent,this);this.options.trackResize&&o.DomEvent[e](t,"resize",this._onResize,this)}},_onResize:function(){o.Util.cancelAnimFrame(this._resizeRequest),this._resizeRequest=o.Util.requestAnimFrame(function(){this.invalidateSize({debounceMoveend:!0})},this,!1,this._container)},_onMouseClick:function(t){!this._loaded||!t._simulated&&(this.dragging&&this.dragging.moved()||this.boxZoom&&this.boxZoom.moved())||o.DomEvent._skipped(t)||(this.fire("preclick"),this._fireMouseEvent(t))},_fireMouseEvent:function(t){if(this._loaded&&!o.DomEvent._skipped(t)){var e=t.type;if(e="mouseenter"===e?"mouseover":"mouseleave"===e?"mouseout":e,this.hasEventListeners(e)){"contextmenu"===e&&o.DomEvent.preventDefault(t);var i=this.mouseEventToContainerPoint(t),n=this.containerPointToLayerPoint(i),s=this.layerPointToLatLng(n);this.fire(e,{latlng:s,layerPoint:n,containerPoint:i,originalEvent:t})}}},_onTileLayerLoad:function(){this._tileLayersToLoad--,this._tileLayersNum&&!this._tileLayersToLoad&&this.fire("tilelayersload")},_clearHandlers:function(){for(var t=0,e=this._handlers.length;e>t;t++)this._handlers[t].disable()},whenReady:function(t,e){return this._loaded?t.call(e||this,this):this.on("load",t,e),this},_layerAdd:function(t){t.onAdd(this),this.fire("layeradd",{layer:t})},_getMapPanePos:function(){return o.DomUtil.getPosition(this._mapPane)},_moved:function(){var t=this._getMapPanePos();return t&&!t.equals([0,0])},_getTopLeftPoint:function(){return this.getPixelOrigin().subtract(this._getMapPanePos())},_getNewTopLeftPoint:function(t,e){var i=this.getSize()._divideBy(2);return this.project(t,e)._subtract(i)._round()},_latLngToNewLayerPoint:function(t,e,i){var n=this._getNewTopLeftPoint(i,e).add(this._getMapPanePos());return this.project(t,e)._subtract(n)},_getCenterLayerPoint:function(){return this.containerPointToLayerPoint(this.getSize()._divideBy(2))},_getCenterOffset:function(t){return this.latLngToLayerPoint(t).subtract(this._getCenterLayerPoint())},_limitCenter:function(t,e,i){if(!i)return t;var n=this.project(t,e),s=this.getSize().divideBy(2),a=new o.Bounds(n.subtract(s),n.add(s)),r=this._getBoundsOffset(a,i,e);return this.unproject(n.add(r),e)},_limitOffset:function(t,e){if(!e)return t;var i=this.getPixelBounds(),n=new o.Bounds(i.min.add(t),i.max.add(t));return t.add(this._getBoundsOffset(n,e))},_getBoundsOffset:function(t,e,i){var n=this.project(e.getNorthWest(),i).subtract(t.min),s=this.project(e.getSouthEast(),i).subtract(t.max),a=this._rebound(n.x,-s.x),r=this._rebound(n.y,-s.y);return new o.Point(a,r)},_rebound:function(t,e){return t+e>0?Math.round(t-e)/2:Math.max(0,Math.ceil(t))-Math.max(0,Math.floor(e))},_limitZoom:function(t){var e=this.getMinZoom(),i=this.getMaxZoom();return Math.max(e,Math.min(i,t))}}),o.map=function(t,e){return new o.Map(t,e)},o.Projection.Mercator={MAX_LATITUDE:85.0840591556,R_MINOR:6356752.314245179,R_MAJOR:6378137,project:function(t){var e=o.LatLng.DEG_TO_RAD,i=this.MAX_LATITUDE,n=Math.max(Math.min(i,t.lat),-i),s=this.R_MAJOR,a=this.R_MINOR,r=t.lng*e*s,h=n*e,l=a/s,u=Math.sqrt(1-l*l),c=u*Math.sin(h);c=Math.pow((1-c)/(1+c),.5*u);var d=Math.tan(.5*(.5*Math.PI-h))/c;return h=-s*Math.log(d),new o.Point(r,h)},unproject:function(t){for(var e,i=o.LatLng.RAD_TO_DEG,n=this.R_MAJOR,s=this.R_MINOR,a=t.x*i/n,r=s/n,h=Math.sqrt(1-r*r),l=Math.exp(-t.y/n),u=Math.PI/2-2*Math.atan(l),c=15,d=1e-7,p=c,_=.1;Math.abs(_)>d&&--p>0;)e=h*Math.sin(u),_=Math.PI/2-2*Math.atan(l*Math.pow((1-e)/(1+e),.5*h))-u,u+=_;
return new o.LatLng(u*i,a)}},o.CRS.EPSG3395=o.extend({},o.CRS,{code:"EPSG:3395",projection:o.Projection.Mercator,transformation:function(){var t=o.Projection.Mercator,e=t.R_MAJOR,i=.5/(Math.PI*e);return new o.Transformation(i,.5,-i,.5)}()}),o.TileLayer=o.Class.extend({includes:o.Mixin.Events,options:{minZoom:0,maxZoom:18,tileSize:256,subdomains:"abc",errorTileUrl:"",attribution:"",zoomOffset:0,opacity:1,unloadInvisibleTiles:o.Browser.mobile,updateWhenIdle:o.Browser.mobile},initialize:function(t,e){e=o.setOptions(this,e),e.detectRetina&&o.Browser.retina&&e.maxZoom>0&&(e.tileSize=Math.floor(e.tileSize/2),e.zoomOffset++,e.minZoom>0&&e.minZoom--,this.options.maxZoom--),e.bounds&&(e.bounds=o.latLngBounds(e.bounds)),this._url=t;var i=this.options.subdomains;"string"==typeof i&&(this.options.subdomains=i.split(""))},onAdd:function(t){this._map=t,this._animated=t._zoomAnimated,this._initContainer(),t.on({viewreset:this._reset,moveend:this._update},this),this._animated&&t.on({zoomanim:this._animateZoom,zoomend:this._endZoomAnim},this),this.options.updateWhenIdle||(this._limitedUpdate=o.Util.limitExecByInterval(this._update,150,this),t.on("move",this._limitedUpdate,this)),this._reset(),this._update()},addTo:function(t){return t.addLayer(this),this},onRemove:function(t){this._container.parentNode.removeChild(this._container),t.off({viewreset:this._reset,moveend:this._update},this),this._animated&&t.off({zoomanim:this._animateZoom,zoomend:this._endZoomAnim},this),this.options.updateWhenIdle||t.off("move",this._limitedUpdate,this),this._container=null,this._map=null},bringToFront:function(){var t=this._map._panes.tilePane;return this._container&&(t.appendChild(this._container),this._setAutoZIndex(t,Math.max)),this},bringToBack:function(){var t=this._map._panes.tilePane;return this._container&&(t.insertBefore(this._container,t.firstChild),this._setAutoZIndex(t,Math.min)),this},getAttribution:function(){return this.options.attribution},getContainer:function(){return this._container},setOpacity:function(t){return this.options.opacity=t,this._map&&this._updateOpacity(),this},setZIndex:function(t){return this.options.zIndex=t,this._updateZIndex(),this},setUrl:function(t,e){return this._url=t,e||this.redraw(),this},redraw:function(){return this._map&&(this._reset({hard:!0}),this._update()),this},_updateZIndex:function(){this._container&&this.options.zIndex!==i&&(this._container.style.zIndex=this.options.zIndex)},_setAutoZIndex:function(t,e){var i,n,o,s=t.children,a=-e(1/0,-1/0);for(n=0,o=s.length;o>n;n++)s[n]!==this._container&&(i=parseInt(s[n].style.zIndex,10),isNaN(i)||(a=e(a,i)));this.options.zIndex=this._container.style.zIndex=(isFinite(a)?a:0)+e(1,-1)},_updateOpacity:function(){var t,e=this._tiles;if(o.Browser.ielt9)for(t in e)o.DomUtil.setOpacity(e[t],this.options.opacity);else o.DomUtil.setOpacity(this._container,this.options.opacity)},_initContainer:function(){var t=this._map._panes.tilePane;if(!this._container){if(this._container=o.DomUtil.create("div","leaflet-layer"),this._updateZIndex(),this._animated){var e="leaflet-tile-container";this._bgBuffer=o.DomUtil.create("div",e,this._container),this._tileContainer=o.DomUtil.create("div",e,this._container)}else this._tileContainer=this._container;t.appendChild(this._container),this.options.opacity<1&&this._updateOpacity()}},_reset:function(t){for(var e in this._tiles)this.fire("tileunload",{tile:this._tiles[e]});this._tiles={},this._tilesToLoad=0,this.options.reuseTiles&&(this._unusedTiles=[]),this._tileContainer.innerHTML="",this._animated&&t&&t.hard&&this._clearBgBuffer(),this._initContainer()},_getTileSize:function(){var t=this._map,e=t.getZoom()+this.options.zoomOffset,i=this.options.maxNativeZoom,n=this.options.tileSize;return i&&e>i&&(n=Math.round(t.getZoomScale(e)/t.getZoomScale(i)*n)),n},_update:function(){if(this._map){var t=this._map,e=t.getPixelBounds(),i=t.getZoom(),n=this._getTileSize();if(!(i>this.options.maxZoom||i<this.options.minZoom)){var s=o.bounds(e.min.divideBy(n)._floor(),e.max.divideBy(n)._floor());this._addTilesFromCenterOut(s),(this.options.unloadInvisibleTiles||this.options.reuseTiles)&&this._removeOtherTiles(s)}}},_addTilesFromCenterOut:function(t){var i,n,s,a=[],r=t.getCenter();for(i=t.min.y;i<=t.max.y;i++)for(n=t.min.x;n<=t.max.x;n++)s=new o.Point(n,i),this._tileShouldBeLoaded(s)&&a.push(s);var h=a.length;if(0!==h){a.sort(function(t,e){return t.distanceTo(r)-e.distanceTo(r)});var l=e.createDocumentFragment();for(this._tilesToLoad||this.fire("loading"),this._tilesToLoad+=h,n=0;h>n;n++)this._addTile(a[n],l);this._tileContainer.appendChild(l)}},_tileShouldBeLoaded:function(t){if(t.x+":"+t.y in this._tiles)return!1;var e=this.options;if(!e.continuousWorld){var i=this._getWrapTileNum();if(e.noWrap&&(t.x<0||t.x>=i.x)||t.y<0||t.y>=i.y)return!1}if(e.bounds){var n=e.tileSize,o=t.multiplyBy(n),s=o.add([n,n]),a=this._map.unproject(o),r=this._map.unproject(s);if(e.continuousWorld||e.noWrap||(a=a.wrap(),r=r.wrap()),!e.bounds.intersects([a,r]))return!1}return!0},_removeOtherTiles:function(t){var e,i,n,o;for(o in this._tiles)e=o.split(":"),i=parseInt(e[0],10),n=parseInt(e[1],10),(i<t.min.x||i>t.max.x||n<t.min.y||n>t.max.y)&&this._removeTile(o)},_removeTile:function(t){var e=this._tiles[t];this.fire("tileunload",{tile:e,url:e.src}),this.options.reuseTiles?(o.DomUtil.removeClass(e,"leaflet-tile-loaded"),this._unusedTiles.push(e)):e.parentNode===this._tileContainer&&this._tileContainer.removeChild(e),o.Browser.android||(e.onload=null,e.src=o.Util.emptyImageUrl),delete this._tiles[t]},_addTile:function(t,e){var i=this._getTilePos(t),n=this._getTile();o.DomUtil.setPosition(n,i,o.Browser.chrome),this._tiles[t.x+":"+t.y]=n,this._loadTile(n,t),n.parentNode!==this._tileContainer&&e.appendChild(n)},_getZoomForUrl:function(){var t=this.options,e=this._map.getZoom();return t.zoomReverse&&(e=t.maxZoom-e),e+=t.zoomOffset,t.maxNativeZoom?Math.min(e,t.maxNativeZoom):e},_getTilePos:function(t){var e=this._map.getPixelOrigin(),i=this._getTileSize();return t.multiplyBy(i).subtract(e)},getTileUrl:function(t){return o.Util.template(this._url,o.extend({s:this._getSubdomain(t),z:t.z,x:t.x,y:t.y},this.options))},_getWrapTileNum:function(){var t=this._map.options.crs,e=t.getSize(this._map.getZoom());return e.divideBy(this._getTileSize())._floor()},_adjustTilePoint:function(t){var e=this._getWrapTileNum();this.options.continuousWorld||this.options.noWrap||(t.x=(t.x%e.x+e.x)%e.x),this.options.tms&&(t.y=e.y-t.y-1),t.z=this._getZoomForUrl()},_getSubdomain:function(t){var e=Math.abs(t.x+t.y)%this.options.subdomains.length;return this.options.subdomains[e]},_getTile:function(){if(this.options.reuseTiles&&this._unusedTiles.length>0){var t=this._unusedTiles.pop();return this._resetTile(t),t}return this._createTile()},_resetTile:function(){},_createTile:function(){var t=o.DomUtil.create("img","leaflet-tile");return t.style.width=t.style.height=this._getTileSize()+"px",t.galleryimg="no",t.onselectstart=t.onmousemove=o.Util.falseFn,o.Browser.ielt9&&this.options.opacity!==i&&o.DomUtil.setOpacity(t,this.options.opacity),o.Browser.mobileWebkit3d&&(t.style.WebkitBackfaceVisibility="hidden"),t},_loadTile:function(t,e){t._layer=this,t.onload=this._tileOnLoad,t.onerror=this._tileOnError,this._adjustTilePoint(e),t.src=this.getTileUrl(e),this.fire("tileloadstart",{tile:t,url:t.src})},_tileLoaded:function(){this._tilesToLoad--,this._animated&&o.DomUtil.addClass(this._tileContainer,"leaflet-zoom-animated"),this._tilesToLoad||(this.fire("load"),this._animated&&(clearTimeout(this._clearBgBufferTimer),this._clearBgBufferTimer=setTimeout(o.bind(this._clearBgBuffer,this),500)))},_tileOnLoad:function(){var t=this._layer;this.src!==o.Util.emptyImageUrl&&(o.DomUtil.addClass(this,"leaflet-tile-loaded"),t.fire("tileload",{tile:this,url:this.src})),t._tileLoaded()},_tileOnError:function(){var t=this._layer;t.fire("tileerror",{tile:this,url:this.src});var e=t.options.errorTileUrl;e&&(this.src=e),t._tileLoaded()}}),o.tileLayer=function(t,e){return new o.TileLayer(t,e)},o.TileLayer.WMS=o.TileLayer.extend({defaultWmsParams:{service:"WMS",request:"GetMap",version:"1.1.1",layers:"",styles:"",format:"image/jpeg",transparent:!1},initialize:function(t,e){this._url=t;var i=o.extend({},this.defaultWmsParams),n=e.tileSize||this.options.tileSize;i.width=i.height=e.detectRetina&&o.Browser.retina?2*n:n;for(var s in e)this.options.hasOwnProperty(s)||"crs"===s||(i[s]=e[s]);this.wmsParams=i,o.setOptions(this,e)},onAdd:function(t){this._crs=this.options.crs||t.options.crs,this._wmsVersion=parseFloat(this.wmsParams.version);var e=this._wmsVersion>=1.3?"crs":"srs";this.wmsParams[e]=this._crs.code,o.TileLayer.prototype.onAdd.call(this,t)},getTileUrl:function(t){var e=this._map,i=this.options.tileSize,n=t.multiplyBy(i),s=n.add([i,i]),a=this._crs.project(e.unproject(n,t.z)),r=this._crs.project(e.unproject(s,t.z)),h=this._wmsVersion>=1.3&&this._crs===o.CRS.EPSG4326?[r.y,a.x,a.y,r.x].join(","):[a.x,r.y,r.x,a.y].join(","),l=o.Util.template(this._url,{s:this._getSubdomain(t)});return l+o.Util.getParamString(this.wmsParams,l,!0)+"&BBOX="+h},setParams:function(t,e){return o.extend(this.wmsParams,t),e||this.redraw(),this}}),o.tileLayer.wms=function(t,e){return new o.TileLayer.WMS(t,e)},o.TileLayer.Canvas=o.TileLayer.extend({options:{async:!1},initialize:function(t){o.setOptions(this,t)},redraw:function(){this._map&&(this._reset({hard:!0}),this._update());for(var t in this._tiles)this._redrawTile(this._tiles[t]);return this},_redrawTile:function(t){this.drawTile(t,t._tilePoint,this._map._zoom)},_createTile:function(){var t=o.DomUtil.create("canvas","leaflet-tile");return t.width=t.height=this.options.tileSize,t.onselectstart=t.onmousemove=o.Util.falseFn,t},_loadTile:function(t,e){t._layer=this,t._tilePoint=e,this._redrawTile(t),this.options.async||this.tileDrawn(t)},drawTile:function(){},tileDrawn:function(t){this._tileOnLoad.call(t)}}),o.tileLayer.canvas=function(t){return new o.TileLayer.Canvas(t)},o.ImageOverlay=o.Class.extend({includes:o.Mixin.Events,options:{opacity:1},initialize:function(t,e,i){this._url=t,this._bounds=o.latLngBounds(e),o.setOptions(this,i)},onAdd:function(t){this._map=t,this._image||this._initImage(),t._panes.overlayPane.appendChild(this._image),t.on("viewreset",this._reset,this),t.options.zoomAnimation&&o.Browser.any3d&&t.on("zoomanim",this._animateZoom,this),this._reset()},onRemove:function(t){t.getPanes().overlayPane.removeChild(this._image),t.off("viewreset",this._reset,this),t.options.zoomAnimation&&t.off("zoomanim",this._animateZoom,this)},addTo:function(t){return t.addLayer(this),this},setOpacity:function(t){return this.options.opacity=t,this._updateOpacity(),this},bringToFront:function(){return this._image&&this._map._panes.overlayPane.appendChild(this._image),this},bringToBack:function(){var t=this._map._panes.overlayPane;return this._image&&t.insertBefore(this._image,t.firstChild),this},setUrl:function(t){this._url=t,this._image.src=this._url},getAttribution:function(){return this.options.attribution},_initImage:function(){this._image=o.DomUtil.create("img","leaflet-image-layer"),this._map.options.zoomAnimation&&o.Browser.any3d?o.DomUtil.addClass(this._image,"leaflet-zoom-animated"):o.DomUtil.addClass(this._image,"leaflet-zoom-hide"),this._updateOpacity(),o.extend(this._image,{galleryimg:"no",onselectstart:o.Util.falseFn,onmousemove:o.Util.falseFn,onload:o.bind(this._onImageLoad,this),src:this._url})},_animateZoom:function(t){var e=this._map,i=this._image,n=e.getZoomScale(t.zoom),s=this._bounds.getNorthWest(),a=this._bounds.getSouthEast(),r=e._latLngToNewLayerPoint(s,t.zoom,t.center),h=e._latLngToNewLayerPoint(a,t.zoom,t.center)._subtract(r),l=r._add(h._multiplyBy(.5*(1-1/n)));i.style[o.DomUtil.TRANSFORM]=o.DomUtil.getTranslateString(l)+" scale("+n+") "},_reset:function(){var t=this._image,e=this._map.latLngToLayerPoint(this._bounds.getNorthWest()),i=this._map.latLngToLayerPoint(this._bounds.getSouthEast())._subtract(e);o.DomUtil.setPosition(t,e),t.style.width=i.x+"px",t.style.height=i.y+"px"},_onImageLoad:function(){this.fire("load")},_updateOpacity:function(){o.DomUtil.setOpacity(this._image,this.options.opacity)}}),o.imageOverlay=function(t,e,i){return new o.ImageOverlay(t,e,i)},o.Icon=o.Class.extend({options:{className:""},initialize:function(t){o.setOptions(this,t)},createIcon:function(t){return this._createIcon("icon",t)},createShadow:function(t){return this._createIcon("shadow",t)},_createIcon:function(t,e){var i=this._getIconUrl(t);if(!i){if("icon"===t)throw new Error("iconUrl not set in Icon options (see the docs).");return null}var n;return n=e&&"IMG"===e.tagName?this._createImg(i,e):this._createImg(i),this._setIconStyles(n,t),n},_setIconStyles:function(t,e){var i,n=this.options,s=o.point(n[e+"Size"]);i=o.point("shadow"===e?n.shadowAnchor||n.iconAnchor:n.iconAnchor),!i&&s&&(i=s.divideBy(2,!0)),t.className="leaflet-marker-"+e+" "+n.className,i&&(t.style.marginLeft=-i.x+"px",t.style.marginTop=-i.y+"px"),s&&(t.style.width=s.x+"px",t.style.height=s.y+"px")},_createImg:function(t,i){return i=i||e.createElement("img"),i.src=t,i},_getIconUrl:function(t){return o.Browser.retina&&this.options[t+"RetinaUrl"]?this.options[t+"RetinaUrl"]:this.options[t+"Url"]}}),o.icon=function(t){return new o.Icon(t)},o.Icon.Default=o.Icon.extend({options:{iconSize:[25,41],iconAnchor:[12,41],popupAnchor:[1,-34],shadowSize:[41,41]},_getIconUrl:function(t){var e=t+"Url";if(this.options[e])return this.options[e];o.Browser.retina&&"icon"===t&&(t+="-2x");var i=o.Icon.Default.imagePath;if(!i)throw new Error("Couldn't autodetect L.Icon.Default.imagePath, set it manually.");return i+"/marker-"+t+".png"}}),o.Icon.Default.imagePath=function(){var t,i,n,o,s,a=e.getElementsByTagName("script"),r=/[\/^]leaflet[\-\._]?([\w\-\._]*)\.js\??/;for(t=0,i=a.length;i>t;t++)if(n=a[t].src,o=n.match(r))return s=n.split(r)[0],(s?s+"/":"")+"images"}(),o.Marker=o.Class.extend({includes:o.Mixin.Events,options:{icon:new o.Icon.Default,title:"",alt:"",clickable:!0,draggable:!1,keyboard:!0,zIndexOffset:0,opacity:1,riseOnHover:!1,riseOffset:250},initialize:function(t,e){o.setOptions(this,e),this._latlng=o.latLng(t)},onAdd:function(t){this._map=t,t.on("viewreset",this.update,this),this._initIcon(),this.update(),this.fire("add"),t.options.zoomAnimation&&t.options.markerZoomAnimation&&t.on("zoomanim",this._animateZoom,this)},addTo:function(t){return t.addLayer(this),this},onRemove:function(t){this.dragging&&this.dragging.disable(),this._removeIcon(),this._removeShadow(),this.fire("remove"),t.off({viewreset:this.update,zoomanim:this._animateZoom},this),this._map=null},getLatLng:function(){return this._latlng},setLatLng:function(t){return this._latlng=o.latLng(t),this.update(),this.fire("move",{latlng:this._latlng})},setZIndexOffset:function(t){return this.options.zIndexOffset=t,this.update(),this},setIcon:function(t){return this.options.icon=t,this._map&&(this._initIcon(),this.update()),this._popup&&this.bindPopup(this._popup),this},update:function(){if(this._icon){var t=this._map.latLngToLayerPoint(this._latlng).round();this._setPos(t)}return this},_initIcon:function(){var t=this.options,e=this._map,i=e.options.zoomAnimation&&e.options.markerZoomAnimation,n=i?"leaflet-zoom-animated":"leaflet-zoom-hide",s=t.icon.createIcon(this._icon),a=!1;s!==this._icon&&(this._icon&&this._removeIcon(),a=!0,t.title&&(s.title=t.title),t.alt&&(s.alt=t.alt)),o.DomUtil.addClass(s,n),t.keyboard&&(s.tabIndex="0"),this._icon=s,this._initInteraction(),t.riseOnHover&&o.DomEvent.on(s,"mouseover",this._bringToFront,this).on(s,"mouseout",this._resetZIndex,this);var r=t.icon.createShadow(this._shadow),h=!1;r!==this._shadow&&(this._removeShadow(),h=!0),r&&o.DomUtil.addClass(r,n),this._shadow=r,t.opacity<1&&this._updateOpacity();var l=this._map._panes;a&&l.markerPane.appendChild(this._icon),r&&h&&l.shadowPane.appendChild(this._shadow)},_removeIcon:function(){this.options.riseOnHover&&o.DomEvent.off(this._icon,"mouseover",this._bringToFront).off(this._icon,"mouseout",this._resetZIndex),this._map._panes.markerPane.removeChild(this._icon),this._icon=null},_removeShadow:function(){this._shadow&&this._map._panes.shadowPane.removeChild(this._shadow),this._shadow=null},_setPos:function(t){o.DomUtil.setPosition(this._icon,t),this._shadow&&o.DomUtil.setPosition(this._shadow,t),this._zIndex=t.y+this.options.zIndexOffset,this._resetZIndex()},_updateZIndex:function(t){this._icon.style.zIndex=this._zIndex+t},_animateZoom:function(t){var e=this._map._latLngToNewLayerPoint(this._latlng,t.zoom,t.center).round();this._setPos(e)},_initInteraction:function(){if(this.options.clickable){var t=this._icon,e=["dblclick","mousedown","mouseover","mousemove","mouseout","contextmenu"];o.DomUtil.addClass(t,"leaflet-clickable"),o.DomEvent.on(t,"click",this._onMouseClick,this),o.DomEvent.on(t,"keypress",this._onKeyPress,this);for(var i=0;i<e.length;i++)o.DomEvent.on(t,e[i],this._fireMouseEvent,this);o.Handler.MarkerDrag&&(this.dragging=new o.Handler.MarkerDrag(this),this.options.draggable&&this.dragging.enable())}},_onMouseClick:function(t){var e=this.dragging&&this.dragging.moved();(this.hasEventListeners(t.type)||e)&&o.DomEvent.stopPropagation(t),e||(this.dragging&&this.dragging._enabled||!this._map.dragging||!this._map.dragging.moved())&&this.fire(t.type,{originalEvent:t,latlng:this._latlng})},_onKeyPress:function(t){13===t.keyCode&&this.fire("click",{originalEvent:t,latlng:this._latlng})},_fireMouseEvent:function(t){this.fire(t.type,{originalEvent:t,latlng:this._latlng}),"contextmenu"===t.type&&this.hasEventListeners(t.type)&&o.DomEvent.preventDefault(t),"mousedown"!==t.type?o.DomEvent.stopPropagation(t):o.DomEvent.preventDefault(t)},setOpacity:function(t){return this.options.opacity=t,this._map&&this._updateOpacity(),this},_updateOpacity:function(){o.DomUtil.setOpacity(this._icon,this.options.opacity),this._shadow&&o.DomUtil.setOpacity(this._shadow,this.options.opacity)},_bringToFront:function(){this._updateZIndex(this.options.riseOffset)},_resetZIndex:function(){this._updateZIndex(0)}}),o.marker=function(t,e){return new o.Marker(t,e)},o.DivIcon=o.Icon.extend({options:{iconSize:[12,12],className:"leaflet-div-icon",html:!1},createIcon:function(t){var i=t&&"DIV"===t.tagName?t:e.createElement("div"),n=this.options;return i.innerHTML=n.html!==!1?n.html:"",n.bgPos&&(i.style.backgroundPosition=-n.bgPos.x+"px "+-n.bgPos.y+"px"),this._setIconStyles(i,"icon"),i},createShadow:function(){return null}}),o.divIcon=function(t){return new o.DivIcon(t)},o.Map.mergeOptions({closePopupOnClick:!0}),o.Popup=o.Class.extend({includes:o.Mixin.Events,options:{minWidth:50,maxWidth:300,autoPan:!0,closeButton:!0,offset:[0,7],autoPanPadding:[5,5],keepInView:!1,className:"",zoomAnimation:!0},initialize:function(t,e){o.setOptions(this,t),this._source=e,this._animated=o.Browser.any3d&&this.options.zoomAnimation,this._isOpen=!1},onAdd:function(t){this._map=t,this._container||this._initLayout();var e=t.options.fadeAnimation;e&&o.DomUtil.setOpacity(this._container,0),t._panes.popupPane.appendChild(this._container),t.on(this._getEvents(),this),this.update(),e&&o.DomUtil.setOpacity(this._container,1),this.fire("open"),t.fire("popupopen",{popup:this}),this._source&&this._source.fire("popupopen",{popup:this})},addTo:function(t){return t.addLayer(this),this},openOn:function(t){return t.openPopup(this),this},onRemove:function(t){t._panes.popupPane.removeChild(this._container),o.Util.falseFn(this._container.offsetWidth),t.off(this._getEvents(),this),t.options.fadeAnimation&&o.DomUtil.setOpacity(this._container,0),this._map=null,this.fire("close"),t.fire("popupclose",{popup:this}),this._source&&this._source.fire("popupclose",{popup:this})},getLatLng:function(){return this._latlng},setLatLng:function(t){return this._latlng=o.latLng(t),this._map&&(this._updatePosition(),this._adjustPan()),this},getContent:function(){return this._content},setContent:function(t){return this._content=t,this.update(),this},update:function(){this._map&&(this._container.style.visibility="hidden",this._updateContent(),this._updateLayout(),this._updatePosition(),this._container.style.visibility="",this._adjustPan())},_getEvents:function(){var t={viewreset:this._updatePosition};return this._animated&&(t.zoomanim=this._zoomAnimation),("closeOnClick"in this.options?this.options.closeOnClick:this._map.options.closePopupOnClick)&&(t.preclick=this._close),this.options.keepInView&&(t.moveend=this._adjustPan),t},_close:function(){this._map&&this._map.closePopup(this)},_initLayout:function(){var t,e="leaflet-popup",i=e+" "+this.options.className+" leaflet-zoom-"+(this._animated?"animated":"hide"),n=this._container=o.DomUtil.create("div",i);this.options.closeButton&&(t=this._closeButton=o.DomUtil.create("a",e+"-close-button",n),t.href="#close",t.innerHTML="&#215;",o.DomEvent.disableClickPropagation(t),o.DomEvent.on(t,"click",this._onCloseButtonClick,this));var s=this._wrapper=o.DomUtil.create("div",e+"-content-wrapper",n);o.DomEvent.disableClickPropagation(s),this._contentNode=o.DomUtil.create("div",e+"-content",s),o.DomEvent.disableScrollPropagation(this._contentNode),o.DomEvent.on(s,"contextmenu",o.DomEvent.stopPropagation),this._tipContainer=o.DomUtil.create("div",e+"-tip-container",n),this._tip=o.DomUtil.create("div",e+"-tip",this._tipContainer)},_updateContent:function(){if(this._content){if("string"==typeof this._content)this._contentNode.innerHTML=this._content;else{for(;this._contentNode.hasChildNodes();)this._contentNode.removeChild(this._contentNode.firstChild);this._contentNode.appendChild(this._content)}this.fire("contentupdate")}},_updateLayout:function(){var t=this._contentNode,e=t.style;e.width="",e.whiteSpace="nowrap";var i=t.offsetWidth;i=Math.min(i,this.options.maxWidth),i=Math.max(i,this.options.minWidth),e.width=i+1+"px",e.whiteSpace="",e.height="";var n=t.offsetHeight,s=this.options.maxHeight,a="leaflet-popup-scrolled";s&&n>s?(e.height=s+"px",o.DomUtil.addClass(t,a)):o.DomUtil.removeClass(t,a),this._containerWidth=this._container.offsetWidth},_updatePosition:function(){if(this._map){var t=this._map.latLngToLayerPoint(this._latlng),e=this._animated,i=o.point(this.options.offset);e&&o.DomUtil.setPosition(this._container,t),this._containerBottom=-i.y-(e?0:t.y),this._containerLeft=-Math.round(this._containerWidth/2)+i.x+(e?0:t.x),this._container.style.bottom=this._containerBottom+"px",this._container.style.left=this._containerLeft+"px"}},_zoomAnimation:function(t){var e=this._map._latLngToNewLayerPoint(this._latlng,t.zoom,t.center);o.DomUtil.setPosition(this._container,e)},_adjustPan:function(){if(this.options.autoPan){var t=this._map,e=this._container.offsetHeight,i=this._containerWidth,n=new o.Point(this._containerLeft,-e-this._containerBottom);this._animated&&n._add(o.DomUtil.getPosition(this._container));var s=t.layerPointToContainerPoint(n),a=o.point(this.options.autoPanPadding),r=o.point(this.options.autoPanPaddingTopLeft||a),h=o.point(this.options.autoPanPaddingBottomRight||a),l=t.getSize(),u=0,c=0;s.x+i+h.x>l.x&&(u=s.x+i-l.x+h.x),s.x-u-r.x<0&&(u=s.x-r.x),s.y+e+h.y>l.y&&(c=s.y+e-l.y+h.y),s.y-c-r.y<0&&(c=s.y-r.y),(u||c)&&t.fire("autopanstart").panBy([u,c])}},_onCloseButtonClick:function(t){this._close(),o.DomEvent.stop(t)}}),o.popup=function(t,e){return new o.Popup(t,e)},o.Map.include({openPopup:function(t,e,i){if(this.closePopup(),!(t instanceof o.Popup)){var n=t;t=new o.Popup(i).setLatLng(e).setContent(n)}return t._isOpen=!0,this._popup=t,this.addLayer(t)},closePopup:function(t){return t&&t!==this._popup||(t=this._popup,this._popup=null),t&&(this.removeLayer(t),t._isOpen=!1),this}}),o.Marker.include({openPopup:function(){return this._popup&&this._map&&!this._map.hasLayer(this._popup)&&(this._popup.setLatLng(this._latlng),this._map.openPopup(this._popup)),this},closePopup:function(){return this._popup&&this._popup._close(),this},togglePopup:function(){return this._popup&&(this._popup._isOpen?this.closePopup():this.openPopup()),this},bindPopup:function(t,e){var i=o.point(this.options.icon.options.popupAnchor||[0,0]);return i=i.add(o.Popup.prototype.options.offset),e&&e.offset&&(i=i.add(e.offset)),e=o.extend({offset:i},e),this._popupHandlersAdded||(this.on("click",this.togglePopup,this).on("remove",this.closePopup,this).on("move",this._movePopup,this),this._popupHandlersAdded=!0),t instanceof o.Popup?(o.setOptions(t,e),this._popup=t):this._popup=new o.Popup(e,this).setContent(t),this},setPopupContent:function(t){return this._popup&&this._popup.setContent(t),this},unbindPopup:function(){return this._popup&&(this._popup=null,this.off("click",this.togglePopup,this).off("remove",this.closePopup,this).off("move",this._movePopup,this),this._popupHandlersAdded=!1),this},getPopup:function(){return this._popup},_movePopup:function(t){this._popup.setLatLng(t.latlng)}}),o.LayerGroup=o.Class.extend({initialize:function(t){this._layers={};var e,i;if(t)for(e=0,i=t.length;i>e;e++)this.addLayer(t[e])},addLayer:function(t){var e=this.getLayerId(t);return this._layers[e]=t,this._map&&this._map.addLayer(t),this},removeLayer:function(t){var e=t in this._layers?t:this.getLayerId(t);return this._map&&this._layers[e]&&this._map.removeLayer(this._layers[e]),delete this._layers[e],this},hasLayer:function(t){return t?t in this._layers||this.getLayerId(t)in this._layers:!1},clearLayers:function(){return this.eachLayer(this.removeLayer,this),this},invoke:function(t){var e,i,n=Array.prototype.slice.call(arguments,1);for(e in this._layers)i=this._layers[e],i[t]&&i[t].apply(i,n);return this},onAdd:function(t){this._map=t,this.eachLayer(t.addLayer,t)},onRemove:function(t){this.eachLayer(t.removeLayer,t),this._map=null},addTo:function(t){return t.addLayer(this),this},eachLayer:function(t,e){for(var i in this._layers)t.call(e,this._layers[i]);return this},getLayer:function(t){return this._layers[t]},getLayers:function(){var t=[];for(var e in this._layers)t.push(this._layers[e]);return t},setZIndex:function(t){return this.invoke("setZIndex",t)},getLayerId:function(t){return o.stamp(t)}}),o.layerGroup=function(t){return new o.LayerGroup(t)},o.FeatureGroup=o.LayerGroup.extend({includes:o.Mixin.Events,statics:{EVENTS:"click dblclick mouseover mouseout mousemove contextmenu popupopen popupclose"},addLayer:function(t){return this.hasLayer(t)?this:("on"in t&&t.on(o.FeatureGroup.EVENTS,this._propagateEvent,this),o.LayerGroup.prototype.addLayer.call(this,t),this._popupContent&&t.bindPopup&&t.bindPopup(this._popupContent,this._popupOptions),this.fire("layeradd",{layer:t}))},removeLayer:function(t){return this.hasLayer(t)?(t in this._layers&&(t=this._layers[t]),t.off(o.FeatureGroup.EVENTS,this._propagateEvent,this),o.LayerGroup.prototype.removeLayer.call(this,t),this._popupContent&&this.invoke("unbindPopup"),this.fire("layerremove",{layer:t})):this},bindPopup:function(t,e){return this._popupContent=t,this._popupOptions=e,this.invoke("bindPopup",t,e)},openPopup:function(t){for(var e in this._layers){this._layers[e].openPopup(t);break}return this},setStyle:function(t){return this.invoke("setStyle",t)},bringToFront:function(){return this.invoke("bringToFront")},bringToBack:function(){return this.invoke("bringToBack")},getBounds:function(){var t=new o.LatLngBounds;return this.eachLayer(function(e){t.extend(e instanceof o.Marker?e.getLatLng():e.getBounds())}),t},_propagateEvent:function(t){t=o.extend({layer:t.target,target:this},t),this.fire(t.type,t)}}),o.featureGroup=function(t){return new o.FeatureGroup(t)},o.Path=o.Class.extend({includes:[o.Mixin.Events],statics:{CLIP_PADDING:function(){var e=o.Browser.mobile?1280:2e3,i=(e/Math.max(t.outerWidth,t.outerHeight)-1)/2;return Math.max(0,Math.min(.5,i))}()},options:{stroke:!0,color:"#0033ff",dashArray:null,lineCap:null,lineJoin:null,weight:5,opacity:.5,fill:!1,fillColor:null,fillOpacity:.2,clickable:!0},initialize:function(t){o.setOptions(this,t)},onAdd:function(t){this._map=t,this._container||(this._initElements(),this._initEvents()),this.projectLatlngs(),this._updatePath(),this._container&&this._map._pathRoot.appendChild(this._container),this.fire("add"),t.on({viewreset:this.projectLatlngs,moveend:this._updatePath},this)},addTo:function(t){return t.addLayer(this),this},onRemove:function(t){t._pathRoot.removeChild(this._container),this.fire("remove"),this._map=null,o.Browser.vml&&(this._container=null,this._stroke=null,this._fill=null),t.off({viewreset:this.projectLatlngs,moveend:this._updatePath},this)},projectLatlngs:function(){},setStyle:function(t){return o.setOptions(this,t),this._container&&this._updateStyle(),this},redraw:function(){return this._map&&(this.projectLatlngs(),this._updatePath()),this}}),o.Map.include({_updatePathViewport:function(){var t=o.Path.CLIP_PADDING,e=this.getSize(),i=o.DomUtil.getPosition(this._mapPane),n=i.multiplyBy(-1)._subtract(e.multiplyBy(t)._round()),s=n.add(e.multiplyBy(1+2*t)._round());this._pathViewport=new o.Bounds(n,s)}}),o.Path.SVG_NS="http://www.w3.org/2000/svg",o.Browser.svg=!(!e.createElementNS||!e.createElementNS(o.Path.SVG_NS,"svg").createSVGRect),o.Path=o.Path.extend({statics:{SVG:o.Browser.svg},bringToFront:function(){var t=this._map._pathRoot,e=this._container;return e&&t.lastChild!==e&&t.appendChild(e),this},bringToBack:function(){var t=this._map._pathRoot,e=this._container,i=t.firstChild;return e&&i!==e&&t.insertBefore(e,i),this},getPathString:function(){},_createElement:function(t){return e.createElementNS(o.Path.SVG_NS,t)},_initElements:function(){this._map._initPathRoot(),this._initPath(),this._initStyle()},_initPath:function(){this._container=this._createElement("g"),this._path=this._createElement("path"),this.options.className&&o.DomUtil.addClass(this._path,this.options.className),this._container.appendChild(this._path)},_initStyle:function(){this.options.stroke&&(this._path.setAttribute("stroke-linejoin","round"),this._path.setAttribute("stroke-linecap","round")),this.options.fill&&this._path.setAttribute("fill-rule","evenodd"),this.options.pointerEvents&&this._path.setAttribute("pointer-events",this.options.pointerEvents),this.options.clickable||this.options.pointerEvents||this._path.setAttribute("pointer-events","none"),this._updateStyle()},_updateStyle:function(){this.options.stroke?(this._path.setAttribute("stroke",this.options.color),this._path.setAttribute("stroke-opacity",this.options.opacity),this._path.setAttribute("stroke-width",this.options.weight),this.options.dashArray?this._path.setAttribute("stroke-dasharray",this.options.dashArray):this._path.removeAttribute("stroke-dasharray"),this.options.lineCap&&this._path.setAttribute("stroke-linecap",this.options.lineCap),this.options.lineJoin&&this._path.setAttribute("stroke-linejoin",this.options.lineJoin)):this._path.setAttribute("stroke","none"),this.options.fill?(this._path.setAttribute("fill",this.options.fillColor||this.options.color),this._path.setAttribute("fill-opacity",this.options.fillOpacity)):this._path.setAttribute("fill","none")},_updatePath:function(){var t=this.getPathString();t||(t="M0 0"),this._path.setAttribute("d",t)},_initEvents:function(){if(this.options.clickable){(o.Browser.svg||!o.Browser.vml)&&o.DomUtil.addClass(this._path,"leaflet-clickable"),o.DomEvent.on(this._container,"click",this._onMouseClick,this);for(var t=["dblclick","mousedown","mouseover","mouseout","mousemove","contextmenu"],e=0;e<t.length;e++)o.DomEvent.on(this._container,t[e],this._fireMouseEvent,this)}},_onMouseClick:function(t){this._map.dragging&&this._map.dragging.moved()||this._fireMouseEvent(t)},_fireMouseEvent:function(t){if(this.hasEventListeners(t.type)){var e=this._map,i=e.mouseEventToContainerPoint(t),n=e.containerPointToLayerPoint(i),s=e.layerPointToLatLng(n);this.fire(t.type,{latlng:s,layerPoint:n,containerPoint:i,originalEvent:t}),"contextmenu"===t.type&&o.DomEvent.preventDefault(t),"mousemove"!==t.type&&o.DomEvent.stopPropagation(t)}}}),o.Map.include({_initPathRoot:function(){this._pathRoot||(this._pathRoot=o.Path.prototype._createElement("svg"),this._panes.overlayPane.appendChild(this._pathRoot),this.options.zoomAnimation&&o.Browser.any3d?(o.DomUtil.addClass(this._pathRoot,"leaflet-zoom-animated"),this.on({zoomanim:this._animatePathZoom,zoomend:this._endPathZoom})):o.DomUtil.addClass(this._pathRoot,"leaflet-zoom-hide"),this.on("moveend",this._updateSvgViewport),this._updateSvgViewport())
},_animatePathZoom:function(t){var e=this.getZoomScale(t.zoom),i=this._getCenterOffset(t.center)._multiplyBy(-e)._add(this._pathViewport.min);this._pathRoot.style[o.DomUtil.TRANSFORM]=o.DomUtil.getTranslateString(i)+" scale("+e+") ",this._pathZooming=!0},_endPathZoom:function(){this._pathZooming=!1},_updateSvgViewport:function(){if(!this._pathZooming){this._updatePathViewport();var t=this._pathViewport,e=t.min,i=t.max,n=i.x-e.x,s=i.y-e.y,a=this._pathRoot,r=this._panes.overlayPane;o.Browser.mobileWebkit&&r.removeChild(a),o.DomUtil.setPosition(a,e),a.setAttribute("width",n),a.setAttribute("height",s),a.setAttribute("viewBox",[e.x,e.y,n,s].join(" ")),o.Browser.mobileWebkit&&r.appendChild(a)}}}),o.Path.include({bindPopup:function(t,e){return t instanceof o.Popup?this._popup=t:((!this._popup||e)&&(this._popup=new o.Popup(e,this)),this._popup.setContent(t)),this._popupHandlersAdded||(this.on("click",this._openPopup,this).on("remove",this.closePopup,this),this._popupHandlersAdded=!0),this},unbindPopup:function(){return this._popup&&(this._popup=null,this.off("click",this._openPopup).off("remove",this.closePopup),this._popupHandlersAdded=!1),this},openPopup:function(t){return this._popup&&(t=t||this._latlng||this._latlngs[Math.floor(this._latlngs.length/2)],this._openPopup({latlng:t})),this},closePopup:function(){return this._popup&&this._popup._close(),this},_openPopup:function(t){this._popup.setLatLng(t.latlng),this._map.openPopup(this._popup)}}),o.Browser.vml=!o.Browser.svg&&function(){try{var t=e.createElement("div");t.innerHTML='<v:shape adj="1"/>';var i=t.firstChild;return i.style.behavior="url(#default#VML)",i&&"object"==typeof i.adj}catch(n){return!1}}(),o.Path=o.Browser.svg||!o.Browser.vml?o.Path:o.Path.extend({statics:{VML:!0,CLIP_PADDING:.02},_createElement:function(){try{return e.namespaces.add("lvml","urn:schemas-microsoft-com:vml"),function(t){return e.createElement("<lvml:"+t+' class="lvml">')}}catch(t){return function(t){return e.createElement("<"+t+' xmlns="urn:schemas-microsoft.com:vml" class="lvml">')}}}(),_initPath:function(){var t=this._container=this._createElement("shape");o.DomUtil.addClass(t,"leaflet-vml-shape"+(this.options.className?" "+this.options.className:"")),this.options.clickable&&o.DomUtil.addClass(t,"leaflet-clickable"),t.coordsize="1 1",this._path=this._createElement("path"),t.appendChild(this._path),this._map._pathRoot.appendChild(t)},_initStyle:function(){this._updateStyle()},_updateStyle:function(){var t=this._stroke,e=this._fill,i=this.options,n=this._container;n.stroked=i.stroke,n.filled=i.fill,i.stroke?(t||(t=this._stroke=this._createElement("stroke"),t.endcap="round",n.appendChild(t)),t.weight=i.weight+"px",t.color=i.color,t.opacity=i.opacity,t.dashStyle=i.dashArray?o.Util.isArray(i.dashArray)?i.dashArray.join(" "):i.dashArray.replace(/( *, *)/g," "):"",i.lineCap&&(t.endcap=i.lineCap.replace("butt","flat")),i.lineJoin&&(t.joinstyle=i.lineJoin)):t&&(n.removeChild(t),this._stroke=null),i.fill?(e||(e=this._fill=this._createElement("fill"),n.appendChild(e)),e.color=i.fillColor||i.color,e.opacity=i.fillOpacity):e&&(n.removeChild(e),this._fill=null)},_updatePath:function(){var t=this._container.style;t.display="none",this._path.v=this.getPathString()+" ",t.display=""}}),o.Map.include(o.Browser.svg||!o.Browser.vml?{}:{_initPathRoot:function(){if(!this._pathRoot){var t=this._pathRoot=e.createElement("div");t.className="leaflet-vml-container",this._panes.overlayPane.appendChild(t),this.on("moveend",this._updatePathViewport),this._updatePathViewport()}}}),o.Browser.canvas=function(){return!!e.createElement("canvas").getContext}(),o.Path=o.Path.SVG&&!t.L_PREFER_CANVAS||!o.Browser.canvas?o.Path:o.Path.extend({statics:{CANVAS:!0,SVG:!1},redraw:function(){return this._map&&(this.projectLatlngs(),this._requestUpdate()),this},setStyle:function(t){return o.setOptions(this,t),this._map&&(this._updateStyle(),this._requestUpdate()),this},onRemove:function(t){t.off("viewreset",this.projectLatlngs,this).off("moveend",this._updatePath,this),this.options.clickable&&(this._map.off("click",this._onClick,this),this._map.off("mousemove",this._onMouseMove,this)),this._requestUpdate(),this.fire("remove"),this._map=null},_requestUpdate:function(){this._map&&!o.Path._updateRequest&&(o.Path._updateRequest=o.Util.requestAnimFrame(this._fireMapMoveEnd,this._map))},_fireMapMoveEnd:function(){o.Path._updateRequest=null,this.fire("moveend")},_initElements:function(){this._map._initPathRoot(),this._ctx=this._map._canvasCtx},_updateStyle:function(){var t=this.options;t.stroke&&(this._ctx.lineWidth=t.weight,this._ctx.strokeStyle=t.color),t.fill&&(this._ctx.fillStyle=t.fillColor||t.color)},_drawPath:function(){var t,e,i,n,s,a;for(this._ctx.beginPath(),t=0,i=this._parts.length;i>t;t++){for(e=0,n=this._parts[t].length;n>e;e++)s=this._parts[t][e],a=(0===e?"move":"line")+"To",this._ctx[a](s.x,s.y);this instanceof o.Polygon&&this._ctx.closePath()}},_checkIfEmpty:function(){return!this._parts.length},_updatePath:function(){if(!this._checkIfEmpty()){var t=this._ctx,e=this.options;this._drawPath(),t.save(),this._updateStyle(),e.fill&&(t.globalAlpha=e.fillOpacity,t.fill()),e.stroke&&(t.globalAlpha=e.opacity,t.stroke()),t.restore()}},_initEvents:function(){this.options.clickable&&(this._map.on("mousemove",this._onMouseMove,this),this._map.on("click",this._onClick,this))},_onClick:function(t){this._containsPoint(t.layerPoint)&&this.fire("click",t)},_onMouseMove:function(t){this._map&&!this._map._animatingZoom&&(this._containsPoint(t.layerPoint)?(this._ctx.canvas.style.cursor="pointer",this._mouseInside=!0,this.fire("mouseover",t)):this._mouseInside&&(this._ctx.canvas.style.cursor="",this._mouseInside=!1,this.fire("mouseout",t)))}}),o.Map.include(o.Path.SVG&&!t.L_PREFER_CANVAS||!o.Browser.canvas?{}:{_initPathRoot:function(){var t,i=this._pathRoot;i||(i=this._pathRoot=e.createElement("canvas"),i.style.position="absolute",t=this._canvasCtx=i.getContext("2d"),t.lineCap="round",t.lineJoin="round",this._panes.overlayPane.appendChild(i),this.options.zoomAnimation&&(this._pathRoot.className="leaflet-zoom-animated",this.on("zoomanim",this._animatePathZoom),this.on("zoomend",this._endPathZoom)),this.on("moveend",this._updateCanvasViewport),this._updateCanvasViewport())},_updateCanvasViewport:function(){if(!this._pathZooming){this._updatePathViewport();var t=this._pathViewport,e=t.min,i=t.max.subtract(e),n=this._pathRoot;o.DomUtil.setPosition(n,e),n.width=i.x,n.height=i.y,n.getContext("2d").translate(-e.x,-e.y)}}}),o.LineUtil={simplify:function(t,e){if(!e||!t.length)return t.slice();var i=e*e;return t=this._reducePoints(t,i),t=this._simplifyDP(t,i)},pointToSegmentDistance:function(t,e,i){return Math.sqrt(this._sqClosestPointOnSegment(t,e,i,!0))},closestPointOnSegment:function(t,e,i){return this._sqClosestPointOnSegment(t,e,i)},_simplifyDP:function(t,e){var n=t.length,o=typeof Uint8Array!=i+""?Uint8Array:Array,s=new o(n);s[0]=s[n-1]=1,this._simplifyDPStep(t,s,e,0,n-1);var a,r=[];for(a=0;n>a;a++)s[a]&&r.push(t[a]);return r},_simplifyDPStep:function(t,e,i,n,o){var s,a,r,h=0;for(a=n+1;o-1>=a;a++)r=this._sqClosestPointOnSegment(t[a],t[n],t[o],!0),r>h&&(s=a,h=r);h>i&&(e[s]=1,this._simplifyDPStep(t,e,i,n,s),this._simplifyDPStep(t,e,i,s,o))},_reducePoints:function(t,e){for(var i=[t[0]],n=1,o=0,s=t.length;s>n;n++)this._sqDist(t[n],t[o])>e&&(i.push(t[n]),o=n);return s-1>o&&i.push(t[s-1]),i},clipSegment:function(t,e,i,n){var o,s,a,r=n?this._lastCode:this._getBitCode(t,i),h=this._getBitCode(e,i);for(this._lastCode=h;;){if(!(r|h))return[t,e];if(r&h)return!1;o=r||h,s=this._getEdgeIntersection(t,e,o,i),a=this._getBitCode(s,i),o===r?(t=s,r=a):(e=s,h=a)}},_getEdgeIntersection:function(t,e,i,n){var s=e.x-t.x,a=e.y-t.y,r=n.min,h=n.max;return 8&i?new o.Point(t.x+s*(h.y-t.y)/a,h.y):4&i?new o.Point(t.x+s*(r.y-t.y)/a,r.y):2&i?new o.Point(h.x,t.y+a*(h.x-t.x)/s):1&i?new o.Point(r.x,t.y+a*(r.x-t.x)/s):void 0},_getBitCode:function(t,e){var i=0;return t.x<e.min.x?i|=1:t.x>e.max.x&&(i|=2),t.y<e.min.y?i|=4:t.y>e.max.y&&(i|=8),i},_sqDist:function(t,e){var i=e.x-t.x,n=e.y-t.y;return i*i+n*n},_sqClosestPointOnSegment:function(t,e,i,n){var s,a=e.x,r=e.y,h=i.x-a,l=i.y-r,u=h*h+l*l;return u>0&&(s=((t.x-a)*h+(t.y-r)*l)/u,s>1?(a=i.x,r=i.y):s>0&&(a+=h*s,r+=l*s)),h=t.x-a,l=t.y-r,n?h*h+l*l:new o.Point(a,r)}},o.Polyline=o.Path.extend({initialize:function(t,e){o.Path.prototype.initialize.call(this,e),this._latlngs=this._convertLatLngs(t)},options:{smoothFactor:1,noClip:!1},projectLatlngs:function(){this._originalPoints=[];for(var t=0,e=this._latlngs.length;e>t;t++)this._originalPoints[t]=this._map.latLngToLayerPoint(this._latlngs[t])},getPathString:function(){for(var t=0,e=this._parts.length,i="";e>t;t++)i+=this._getPathPartStr(this._parts[t]);return i},getLatLngs:function(){return this._latlngs},setLatLngs:function(t){return this._latlngs=this._convertLatLngs(t),this.redraw()},addLatLng:function(t){return this._latlngs.push(o.latLng(t)),this.redraw()},spliceLatLngs:function(){var t=[].splice.apply(this._latlngs,arguments);return this._convertLatLngs(this._latlngs,!0),this.redraw(),t},closestLayerPoint:function(t){for(var e,i,n=1/0,s=this._parts,a=null,r=0,h=s.length;h>r;r++)for(var l=s[r],u=1,c=l.length;c>u;u++){e=l[u-1],i=l[u];var d=o.LineUtil._sqClosestPointOnSegment(t,e,i,!0);n>d&&(n=d,a=o.LineUtil._sqClosestPointOnSegment(t,e,i))}return a&&(a.distance=Math.sqrt(n)),a},getBounds:function(){return new o.LatLngBounds(this.getLatLngs())},_convertLatLngs:function(t,e){var i,n,s=e?t:[];for(i=0,n=t.length;n>i;i++){if(o.Util.isArray(t[i])&&"number"!=typeof t[i][0])return;s[i]=o.latLng(t[i])}return s},_initEvents:function(){o.Path.prototype._initEvents.call(this)},_getPathPartStr:function(t){for(var e,i=o.Path.VML,n=0,s=t.length,a="";s>n;n++)e=t[n],i&&e._round(),a+=(n?"L":"M")+e.x+" "+e.y;return a},_clipPoints:function(){var t,e,i,n=this._originalPoints,s=n.length;if(this.options.noClip)return void(this._parts=[n]);this._parts=[];var a=this._parts,r=this._map._pathViewport,h=o.LineUtil;for(t=0,e=0;s-1>t;t++)i=h.clipSegment(n[t],n[t+1],r,t),i&&(a[e]=a[e]||[],a[e].push(i[0]),(i[1]!==n[t+1]||t===s-2)&&(a[e].push(i[1]),e++))},_simplifyPoints:function(){for(var t=this._parts,e=o.LineUtil,i=0,n=t.length;n>i;i++)t[i]=e.simplify(t[i],this.options.smoothFactor)},_updatePath:function(){this._map&&(this._clipPoints(),this._simplifyPoints(),o.Path.prototype._updatePath.call(this))}}),o.polyline=function(t,e){return new o.Polyline(t,e)},o.PolyUtil={},o.PolyUtil.clipPolygon=function(t,e){var i,n,s,a,r,h,l,u,c,d=[1,4,2,8],p=o.LineUtil;for(n=0,l=t.length;l>n;n++)t[n]._code=p._getBitCode(t[n],e);for(a=0;4>a;a++){for(u=d[a],i=[],n=0,l=t.length,s=l-1;l>n;s=n++)r=t[n],h=t[s],r._code&u?h._code&u||(c=p._getEdgeIntersection(h,r,u,e),c._code=p._getBitCode(c,e),i.push(c)):(h._code&u&&(c=p._getEdgeIntersection(h,r,u,e),c._code=p._getBitCode(c,e),i.push(c)),i.push(r));t=i}return t},o.Polygon=o.Polyline.extend({options:{fill:!0},initialize:function(t,e){o.Polyline.prototype.initialize.call(this,t,e),this._initWithHoles(t)},_initWithHoles:function(t){var e,i,n;if(t&&o.Util.isArray(t[0])&&"number"!=typeof t[0][0])for(this._latlngs=this._convertLatLngs(t[0]),this._holes=t.slice(1),e=0,i=this._holes.length;i>e;e++)n=this._holes[e]=this._convertLatLngs(this._holes[e]),n[0].equals(n[n.length-1])&&n.pop();t=this._latlngs,t.length>=2&&t[0].equals(t[t.length-1])&&t.pop()},projectLatlngs:function(){if(o.Polyline.prototype.projectLatlngs.call(this),this._holePoints=[],this._holes){var t,e,i,n;for(t=0,i=this._holes.length;i>t;t++)for(this._holePoints[t]=[],e=0,n=this._holes[t].length;n>e;e++)this._holePoints[t][e]=this._map.latLngToLayerPoint(this._holes[t][e])}},setLatLngs:function(t){return t&&o.Util.isArray(t[0])&&"number"!=typeof t[0][0]?(this._initWithHoles(t),this.redraw()):o.Polyline.prototype.setLatLngs.call(this,t)},_clipPoints:function(){var t=this._originalPoints,e=[];if(this._parts=[t].concat(this._holePoints),!this.options.noClip){for(var i=0,n=this._parts.length;n>i;i++){var s=o.PolyUtil.clipPolygon(this._parts[i],this._map._pathViewport);s.length&&e.push(s)}this._parts=e}},_getPathPartStr:function(t){var e=o.Polyline.prototype._getPathPartStr.call(this,t);return e+(o.Browser.svg?"z":"x")}}),o.polygon=function(t,e){return new o.Polygon(t,e)},function(){function t(t){return o.FeatureGroup.extend({initialize:function(t,e){this._layers={},this._options=e,this.setLatLngs(t)},setLatLngs:function(e){var i=0,n=e.length;for(this.eachLayer(function(t){n>i?t.setLatLngs(e[i++]):this.removeLayer(t)},this);n>i;)this.addLayer(new t(e[i++],this._options));return this},getLatLngs:function(){var t=[];return this.eachLayer(function(e){t.push(e.getLatLngs())}),t}})}o.MultiPolyline=t(o.Polyline),o.MultiPolygon=t(o.Polygon),o.multiPolyline=function(t,e){return new o.MultiPolyline(t,e)},o.multiPolygon=function(t,e){return new o.MultiPolygon(t,e)}}(),o.Rectangle=o.Polygon.extend({initialize:function(t,e){o.Polygon.prototype.initialize.call(this,this._boundsToLatLngs(t),e)},setBounds:function(t){this.setLatLngs(this._boundsToLatLngs(t))},_boundsToLatLngs:function(t){return t=o.latLngBounds(t),[t.getSouthWest(),t.getNorthWest(),t.getNorthEast(),t.getSouthEast()]}}),o.rectangle=function(t,e){return new o.Rectangle(t,e)},o.Circle=o.Path.extend({initialize:function(t,e,i){o.Path.prototype.initialize.call(this,i),this._latlng=o.latLng(t),this._mRadius=e},options:{fill:!0},setLatLng:function(t){return this._latlng=o.latLng(t),this.redraw()},setRadius:function(t){return this._mRadius=t,this.redraw()},projectLatlngs:function(){var t=this._getLngRadius(),e=this._latlng,i=this._map.latLngToLayerPoint([e.lat,e.lng-t]);this._point=this._map.latLngToLayerPoint(e),this._radius=Math.max(this._point.x-i.x,1)},getBounds:function(){var t=this._getLngRadius(),e=this._mRadius/40075017*360,i=this._latlng;return new o.LatLngBounds([i.lat-e,i.lng-t],[i.lat+e,i.lng+t])},getLatLng:function(){return this._latlng},getPathString:function(){var t=this._point,e=this._radius;return this._checkIfEmpty()?"":o.Browser.svg?"M"+t.x+","+(t.y-e)+"A"+e+","+e+",0,1,1,"+(t.x-.1)+","+(t.y-e)+" z":(t._round(),e=Math.round(e),"AL "+t.x+","+t.y+" "+e+","+e+" 0,23592600")},getRadius:function(){return this._mRadius},_getLatRadius:function(){return this._mRadius/40075017*360},_getLngRadius:function(){return this._getLatRadius()/Math.cos(o.LatLng.DEG_TO_RAD*this._latlng.lat)},_checkIfEmpty:function(){if(!this._map)return!1;var t=this._map._pathViewport,e=this._radius,i=this._point;return i.x-e>t.max.x||i.y-e>t.max.y||i.x+e<t.min.x||i.y+e<t.min.y}}),o.circle=function(t,e,i){return new o.Circle(t,e,i)},o.CircleMarker=o.Circle.extend({options:{radius:10,weight:2},initialize:function(t,e){o.Circle.prototype.initialize.call(this,t,null,e),this._radius=this.options.radius},projectLatlngs:function(){this._point=this._map.latLngToLayerPoint(this._latlng)},_updateStyle:function(){o.Circle.prototype._updateStyle.call(this),this.setRadius(this.options.radius)},setLatLng:function(t){return o.Circle.prototype.setLatLng.call(this,t),this._popup&&this._popup._isOpen&&this._popup.setLatLng(t),this},setRadius:function(t){return this.options.radius=this._radius=t,this.redraw()},getRadius:function(){return this._radius}}),o.circleMarker=function(t,e){return new o.CircleMarker(t,e)},o.Polyline.include(o.Path.CANVAS?{_containsPoint:function(t,e){var i,n,s,a,r,h,l,u=this.options.weight/2;for(o.Browser.touch&&(u+=10),i=0,a=this._parts.length;a>i;i++)for(l=this._parts[i],n=0,r=l.length,s=r-1;r>n;s=n++)if((e||0!==n)&&(h=o.LineUtil.pointToSegmentDistance(t,l[s],l[n]),u>=h))return!0;return!1}}:{}),o.Polygon.include(o.Path.CANVAS?{_containsPoint:function(t){var e,i,n,s,a,r,h,l,u=!1;if(o.Polyline.prototype._containsPoint.call(this,t,!0))return!0;for(s=0,h=this._parts.length;h>s;s++)for(e=this._parts[s],a=0,l=e.length,r=l-1;l>a;r=a++)i=e[a],n=e[r],i.y>t.y!=n.y>t.y&&t.x<(n.x-i.x)*(t.y-i.y)/(n.y-i.y)+i.x&&(u=!u);return u}}:{}),o.Circle.include(o.Path.CANVAS?{_drawPath:function(){var t=this._point;this._ctx.beginPath(),this._ctx.arc(t.x,t.y,this._radius,0,2*Math.PI,!1)},_containsPoint:function(t){var e=this._point,i=this.options.stroke?this.options.weight/2:0;return t.distanceTo(e)<=this._radius+i}}:{}),o.CircleMarker.include(o.Path.CANVAS?{_updateStyle:function(){o.Path.prototype._updateStyle.call(this)}}:{}),o.GeoJSON=o.FeatureGroup.extend({initialize:function(t,e){o.setOptions(this,e),this._layers={},t&&this.addData(t)},addData:function(t){var e,i,n,s=o.Util.isArray(t)?t:t.features;if(s){for(e=0,i=s.length;i>e;e++)n=s[e],(n.geometries||n.geometry||n.features||n.coordinates)&&this.addData(s[e]);return this}var a=this.options;if(!a.filter||a.filter(t)){var r=o.GeoJSON.geometryToLayer(t,a.pointToLayer,a.coordsToLatLng,a);return r.feature=o.GeoJSON.asFeature(t),r.defaultOptions=r.options,this.resetStyle(r),a.onEachFeature&&a.onEachFeature(t,r),this.addLayer(r)}},resetStyle:function(t){var e=this.options.style;e&&(o.Util.extend(t.options,t.defaultOptions),this._setLayerStyle(t,e))},setStyle:function(t){this.eachLayer(function(e){this._setLayerStyle(e,t)},this)},_setLayerStyle:function(t,e){"function"==typeof e&&(e=e(t.feature)),t.setStyle&&t.setStyle(e)}}),o.extend(o.GeoJSON,{geometryToLayer:function(t,e,i,n){var s,a,r,h,l="Feature"===t.type?t.geometry:t,u=l.coordinates,c=[];switch(i=i||this.coordsToLatLng,l.type){case"Point":return s=i(u),e?e(t,s):new o.Marker(s);case"MultiPoint":for(r=0,h=u.length;h>r;r++)s=i(u[r]),c.push(e?e(t,s):new o.Marker(s));return new o.FeatureGroup(c);case"LineString":return a=this.coordsToLatLngs(u,0,i),new o.Polyline(a,n);case"Polygon":if(2===u.length&&!u[1].length)throw new Error("Invalid GeoJSON object.");return a=this.coordsToLatLngs(u,1,i),new o.Polygon(a,n);case"MultiLineString":return a=this.coordsToLatLngs(u,1,i),new o.MultiPolyline(a,n);case"MultiPolygon":return a=this.coordsToLatLngs(u,2,i),new o.MultiPolygon(a,n);case"GeometryCollection":for(r=0,h=l.geometries.length;h>r;r++)c.push(this.geometryToLayer({geometry:l.geometries[r],type:"Feature",properties:t.properties},e,i,n));return new o.FeatureGroup(c);default:throw new Error("Invalid GeoJSON object.")}},coordsToLatLng:function(t){return new o.LatLng(t[1],t[0],t[2])},coordsToLatLngs:function(t,e,i){var n,o,s,a=[];for(o=0,s=t.length;s>o;o++)n=e?this.coordsToLatLngs(t[o],e-1,i):(i||this.coordsToLatLng)(t[o]),a.push(n);return a},latLngToCoords:function(t){var e=[t.lng,t.lat];return t.alt!==i&&e.push(t.alt),e},latLngsToCoords:function(t){for(var e=[],i=0,n=t.length;n>i;i++)e.push(o.GeoJSON.latLngToCoords(t[i]));return e},getFeature:function(t,e){return t.feature?o.extend({},t.feature,{geometry:e}):o.GeoJSON.asFeature(e)},asFeature:function(t){return"Feature"===t.type?t:{type:"Feature",properties:{},geometry:t}}});var a={toGeoJSON:function(){return o.GeoJSON.getFeature(this,{type:"Point",coordinates:o.GeoJSON.latLngToCoords(this.getLatLng())})}};o.Marker.include(a),o.Circle.include(a),o.CircleMarker.include(a),o.Polyline.include({toGeoJSON:function(){return o.GeoJSON.getFeature(this,{type:"LineString",coordinates:o.GeoJSON.latLngsToCoords(this.getLatLngs())})}}),o.Polygon.include({toGeoJSON:function(){var t,e,i,n=[o.GeoJSON.latLngsToCoords(this.getLatLngs())];if(n[0].push(n[0][0]),this._holes)for(t=0,e=this._holes.length;e>t;t++)i=o.GeoJSON.latLngsToCoords(this._holes[t]),i.push(i[0]),n.push(i);return o.GeoJSON.getFeature(this,{type:"Polygon",coordinates:n})}}),function(){function t(t){return function(){var e=[];return this.eachLayer(function(t){e.push(t.toGeoJSON().geometry.coordinates)}),o.GeoJSON.getFeature(this,{type:t,coordinates:e})}}o.MultiPolyline.include({toGeoJSON:t("MultiLineString")}),o.MultiPolygon.include({toGeoJSON:t("MultiPolygon")}),o.LayerGroup.include({toGeoJSON:function(){var e,i=this.feature&&this.feature.geometry,n=[];if(i&&"MultiPoint"===i.type)return t("MultiPoint").call(this);var s=i&&"GeometryCollection"===i.type;return this.eachLayer(function(t){t.toGeoJSON&&(e=t.toGeoJSON(),n.push(s?e.geometry:o.GeoJSON.asFeature(e)))}),s?o.GeoJSON.getFeature(this,{geometries:n,type:"GeometryCollection"}):{type:"FeatureCollection",features:n}}})}(),o.geoJson=function(t,e){return new o.GeoJSON(t,e)},o.DomEvent={addListener:function(t,e,i,n){var s,a,r,h=o.stamp(i),l="_leaflet_"+e+h;return t[l]?this:(s=function(e){return i.call(n||t,e||o.DomEvent._getEvent())},o.Browser.pointer&&0===e.indexOf("touch")?this.addPointerListener(t,e,s,h):(o.Browser.touch&&"dblclick"===e&&this.addDoubleTapListener&&this.addDoubleTapListener(t,s,h),"addEventListener"in t?"mousewheel"===e?(t.addEventListener("DOMMouseScroll",s,!1),t.addEventListener(e,s,!1)):"mouseenter"===e||"mouseleave"===e?(a=s,r="mouseenter"===e?"mouseover":"mouseout",s=function(e){return o.DomEvent._checkMouse(t,e)?a(e):void 0},t.addEventListener(r,s,!1)):"click"===e&&o.Browser.android?(a=s,s=function(t){return o.DomEvent._filterClick(t,a)},t.addEventListener(e,s,!1)):t.addEventListener(e,s,!1):"attachEvent"in t&&t.attachEvent("on"+e,s),t[l]=s,this))},removeListener:function(t,e,i){var n=o.stamp(i),s="_leaflet_"+e+n,a=t[s];return a?(o.Browser.pointer&&0===e.indexOf("touch")?this.removePointerListener(t,e,n):o.Browser.touch&&"dblclick"===e&&this.removeDoubleTapListener?this.removeDoubleTapListener(t,n):"removeEventListener"in t?"mousewheel"===e?(t.removeEventListener("DOMMouseScroll",a,!1),t.removeEventListener(e,a,!1)):"mouseenter"===e||"mouseleave"===e?t.removeEventListener("mouseenter"===e?"mouseover":"mouseout",a,!1):t.removeEventListener(e,a,!1):"detachEvent"in t&&t.detachEvent("on"+e,a),t[s]=null,this):this},stopPropagation:function(t){return t.stopPropagation?t.stopPropagation():t.cancelBubble=!0,o.DomEvent._skipped(t),this},disableScrollPropagation:function(t){var e=o.DomEvent.stopPropagation;return o.DomEvent.on(t,"mousewheel",e).on(t,"MozMousePixelScroll",e)},disableClickPropagation:function(t){for(var e=o.DomEvent.stopPropagation,i=o.Draggable.START.length-1;i>=0;i--)o.DomEvent.on(t,o.Draggable.START[i],e);return o.DomEvent.on(t,"click",o.DomEvent._fakeStop).on(t,"dblclick",e)},preventDefault:function(t){return t.preventDefault?t.preventDefault():t.returnValue=!1,this},stop:function(t){return o.DomEvent.preventDefault(t).stopPropagation(t)},getMousePosition:function(t,e){if(!e)return new o.Point(t.clientX,t.clientY);var i=e.getBoundingClientRect();return new o.Point(t.clientX-i.left-e.clientLeft,t.clientY-i.top-e.clientTop)},getWheelDelta:function(t){var e=0;return t.wheelDelta&&(e=t.wheelDelta/120),t.detail&&(e=-t.detail/3),e},_skipEvents:{},_fakeStop:function(t){o.DomEvent._skipEvents[t.type]=!0},_skipped:function(t){var e=this._skipEvents[t.type];return this._skipEvents[t.type]=!1,e},_checkMouse:function(t,e){var i=e.relatedTarget;if(!i)return!0;try{for(;i&&i!==t;)i=i.parentNode}catch(n){return!1}return i!==t},_getEvent:function(){var e=t.event;if(!e)for(var i=arguments.callee.caller;i&&(e=i.arguments[0],!e||t.Event!==e.constructor);)i=i.caller;return e},_filterClick:function(t,e){var i=t.timeStamp||t.originalEvent.timeStamp,n=o.DomEvent._lastClick&&i-o.DomEvent._lastClick;return n&&n>100&&500>n||t.target._simulatedClick&&!t._simulated?void o.DomEvent.stop(t):(o.DomEvent._lastClick=i,e(t))}},o.DomEvent.on=o.DomEvent.addListener,o.DomEvent.off=o.DomEvent.removeListener,o.Draggable=o.Class.extend({includes:o.Mixin.Events,statics:{START:o.Browser.touch?["touchstart","mousedown"]:["mousedown"],END:{mousedown:"mouseup",touchstart:"touchend",pointerdown:"touchend",MSPointerDown:"touchend"},MOVE:{mousedown:"mousemove",touchstart:"touchmove",pointerdown:"touchmove",MSPointerDown:"touchmove"}},initialize:function(t,e){this._element=t,this._dragStartTarget=e||t},enable:function(){if(!this._enabled){for(var t=o.Draggable.START.length-1;t>=0;t--)o.DomEvent.on(this._dragStartTarget,o.Draggable.START[t],this._onDown,this);this._enabled=!0}},disable:function(){if(this._enabled){for(var t=o.Draggable.START.length-1;t>=0;t--)o.DomEvent.off(this._dragStartTarget,o.Draggable.START[t],this._onDown,this);this._enabled=!1,this._moved=!1}},_onDown:function(t){if(this._moved=!1,!(t.shiftKey||1!==t.which&&1!==t.button&&!t.touches||(o.DomEvent.stopPropagation(t),o.Draggable._disabled||(o.DomUtil.disableImageDrag(),o.DomUtil.disableTextSelection(),this._moving)))){var i=t.touches?t.touches[0]:t;this._startPoint=new o.Point(i.clientX,i.clientY),this._startPos=this._newPos=o.DomUtil.getPosition(this._element),o.DomEvent.on(e,o.Draggable.MOVE[t.type],this._onMove,this).on(e,o.Draggable.END[t.type],this._onUp,this)}},_onMove:function(t){if(t.touches&&t.touches.length>1)return void(this._moved=!0);var i=t.touches&&1===t.touches.length?t.touches[0]:t,n=new o.Point(i.clientX,i.clientY),s=n.subtract(this._startPoint);(s.x||s.y)&&(o.Browser.touch&&Math.abs(s.x)+Math.abs(s.y)<3||(o.DomEvent.preventDefault(t),this._moved||(this.fire("dragstart"),this._moved=!0,this._startPos=o.DomUtil.getPosition(this._element).subtract(s),o.DomUtil.addClass(e.body,"leaflet-dragging"),this._lastTarget=t.target||t.srcElement,o.DomUtil.addClass(this._lastTarget,"leaflet-drag-target")),this._newPos=this._startPos.add(s),this._moving=!0,o.Util.cancelAnimFrame(this._animRequest),this._animRequest=o.Util.requestAnimFrame(this._updatePosition,this,!0,this._dragStartTarget)))},_updatePosition:function(){this.fire("predrag"),o.DomUtil.setPosition(this._element,this._newPos),this.fire("drag")},_onUp:function(){o.DomUtil.removeClass(e.body,"leaflet-dragging"),this._lastTarget&&(o.DomUtil.removeClass(this._lastTarget,"leaflet-drag-target"),this._lastTarget=null);for(var t in o.Draggable.MOVE)o.DomEvent.off(e,o.Draggable.MOVE[t],this._onMove).off(e,o.Draggable.END[t],this._onUp);o.DomUtil.enableImageDrag(),o.DomUtil.enableTextSelection(),this._moved&&this._moving&&(o.Util.cancelAnimFrame(this._animRequest),this.fire("dragend",{distance:this._newPos.distanceTo(this._startPos)})),this._moving=!1}}),o.Handler=o.Class.extend({initialize:function(t){this._map=t},enable:function(){this._enabled||(this._enabled=!0,this.addHooks())},disable:function(){this._enabled&&(this._enabled=!1,this.removeHooks())},enabled:function(){return!!this._enabled}}),o.Map.mergeOptions({dragging:!0,inertia:!o.Browser.android23,inertiaDeceleration:3400,inertiaMaxSpeed:1/0,inertiaThreshold:o.Browser.touch?32:18,easeLinearity:.25,worldCopyJump:!1}),o.Map.Drag=o.Handler.extend({addHooks:function(){if(!this._draggable){var t=this._map;this._draggable=new o.Draggable(t._mapPane,t._container),this._draggable.on({dragstart:this._onDragStart,drag:this._onDrag,dragend:this._onDragEnd},this),t.options.worldCopyJump&&(this._draggable.on("predrag",this._onPreDrag,this),t.on("viewreset",this._onViewReset,this),t.whenReady(this._onViewReset,this))}this._draggable.enable()},removeHooks:function(){this._draggable.disable()},moved:function(){return this._draggable&&this._draggable._moved},_onDragStart:function(){var t=this._map;t._panAnim&&t._panAnim.stop(),t.fire("movestart").fire("dragstart"),t.options.inertia&&(this._positions=[],this._times=[])},_onDrag:function(){if(this._map.options.inertia){var t=this._lastTime=+new Date,e=this._lastPos=this._draggable._newPos;this._positions.push(e),this._times.push(t),t-this._times[0]>200&&(this._positions.shift(),this._times.shift())}this._map.fire("move").fire("drag")},_onViewReset:function(){var t=this._map.getSize()._divideBy(2),e=this._map.latLngToLayerPoint([0,0]);this._initialWorldOffset=e.subtract(t).x,this._worldWidth=this._map.project([0,180]).x},_onPreDrag:function(){var t=this._worldWidth,e=Math.round(t/2),i=this._initialWorldOffset,n=this._draggable._newPos.x,o=(n-e+i)%t+e-i,s=(n+e+i)%t-e-i,a=Math.abs(o+i)<Math.abs(s+i)?o:s;this._draggable._newPos.x=a},_onDragEnd:function(t){var e=this._map,i=e.options,n=+new Date-this._lastTime,s=!i.inertia||n>i.inertiaThreshold||!this._positions[0];if(e.fire("dragend",t),s)e.fire("moveend");else{var a=this._lastPos.subtract(this._positions[0]),r=(this._lastTime+n-this._times[0])/1e3,h=i.easeLinearity,l=a.multiplyBy(h/r),u=l.distanceTo([0,0]),c=Math.min(i.inertiaMaxSpeed,u),d=l.multiplyBy(c/u),p=c/(i.inertiaDeceleration*h),_=d.multiplyBy(-p/2).round();_.x&&_.y?(_=e._limitOffset(_,e.options.maxBounds),o.Util.requestAnimFrame(function(){e.panBy(_,{duration:p,easeLinearity:h,noMoveStart:!0})})):e.fire("moveend")}}}),o.Map.addInitHook("addHandler","dragging",o.Map.Drag),o.Map.mergeOptions({doubleClickZoom:!0}),o.Map.DoubleClickZoom=o.Handler.extend({addHooks:function(){this._map.on("dblclick",this._onDoubleClick,this)},removeHooks:function(){this._map.off("dblclick",this._onDoubleClick,this)},_onDoubleClick:function(t){var e=this._map,i=e.getZoom()+(t.originalEvent.shiftKey?-1:1);"center"===e.options.doubleClickZoom?e.setZoom(i):e.setZoomAround(t.containerPoint,i)}}),o.Map.addInitHook("addHandler","doubleClickZoom",o.Map.DoubleClickZoom),o.Map.mergeOptions({scrollWheelZoom:!0}),o.Map.ScrollWheelZoom=o.Handler.extend({addHooks:function(){o.DomEvent.on(this._map._container,"mousewheel",this._onWheelScroll,this),o.DomEvent.on(this._map._container,"MozMousePixelScroll",o.DomEvent.preventDefault),this._delta=0},removeHooks:function(){o.DomEvent.off(this._map._container,"mousewheel",this._onWheelScroll),o.DomEvent.off(this._map._container,"MozMousePixelScroll",o.DomEvent.preventDefault)},_onWheelScroll:function(t){var e=o.DomEvent.getWheelDelta(t);this._delta+=e,this._lastMousePos=this._map.mouseEventToContainerPoint(t),this._startTime||(this._startTime=+new Date);var i=Math.max(40-(+new Date-this._startTime),0);clearTimeout(this._timer),this._timer=setTimeout(o.bind(this._performZoom,this),i),o.DomEvent.preventDefault(t),o.DomEvent.stopPropagation(t)},_performZoom:function(){var t=this._map,e=this._delta,i=t.getZoom();e=e>0?Math.ceil(e):Math.floor(e),e=Math.max(Math.min(e,4),-4),e=t._limitZoom(i+e)-i,this._delta=0,this._startTime=null,e&&("center"===t.options.scrollWheelZoom?t.setZoom(i+e):t.setZoomAround(this._lastMousePos,i+e))}}),o.Map.addInitHook("addHandler","scrollWheelZoom",o.Map.ScrollWheelZoom),o.extend(o.DomEvent,{_touchstart:o.Browser.msPointer?"MSPointerDown":o.Browser.pointer?"pointerdown":"touchstart",_touchend:o.Browser.msPointer?"MSPointerUp":o.Browser.pointer?"pointerup":"touchend",addDoubleTapListener:function(t,i,n){function s(t){var e;if(o.Browser.pointer?(_.push(t.pointerId),e=_.length):e=t.touches.length,!(e>1)){var i=Date.now(),n=i-(r||i);h=t.touches?t.touches[0]:t,l=n>0&&u>=n,r=i}}function a(t){if(o.Browser.pointer){var e=_.indexOf(t.pointerId);if(-1===e)return;_.splice(e,1)}if(l){if(o.Browser.pointer){var n,s={};for(var a in h)n=h[a],s[a]="function"==typeof n?n.bind(h):n;h=s}h.type="dblclick",i(h),r=null}}var r,h,l=!1,u=250,c="_leaflet_",d=this._touchstart,p=this._touchend,_=[];t[c+d+n]=s,t[c+p+n]=a;var m=o.Browser.pointer?e.documentElement:t;return t.addEventListener(d,s,!1),m.addEventListener(p,a,!1),o.Browser.pointer&&m.addEventListener(o.DomEvent.POINTER_CANCEL,a,!1),this},removeDoubleTapListener:function(t,i){var n="_leaflet_";return t.removeEventListener(this._touchstart,t[n+this._touchstart+i],!1),(o.Browser.pointer?e.documentElement:t).removeEventListener(this._touchend,t[n+this._touchend+i],!1),o.Browser.pointer&&e.documentElement.removeEventListener(o.DomEvent.POINTER_CANCEL,t[n+this._touchend+i],!1),this}}),o.extend(o.DomEvent,{POINTER_DOWN:o.Browser.msPointer?"MSPointerDown":"pointerdown",POINTER_MOVE:o.Browser.msPointer?"MSPointerMove":"pointermove",POINTER_UP:o.Browser.msPointer?"MSPointerUp":"pointerup",POINTER_CANCEL:o.Browser.msPointer?"MSPointerCancel":"pointercancel",_pointers:[],_pointerDocumentListener:!1,addPointerListener:function(t,e,i,n){switch(e){case"touchstart":return this.addPointerListenerStart(t,e,i,n);case"touchend":return this.addPointerListenerEnd(t,e,i,n);case"touchmove":return this.addPointerListenerMove(t,e,i,n);default:throw"Unknown touch event type"}},addPointerListenerStart:function(t,i,n,s){var a="_leaflet_",r=this._pointers,h=function(t){o.DomEvent.preventDefault(t);for(var e=!1,i=0;i<r.length;i++)if(r[i].pointerId===t.pointerId){e=!0;
break}e||r.push(t),t.touches=r.slice(),t.changedTouches=[t],n(t)};if(t[a+"touchstart"+s]=h,t.addEventListener(this.POINTER_DOWN,h,!1),!this._pointerDocumentListener){var l=function(t){for(var e=0;e<r.length;e++)if(r[e].pointerId===t.pointerId){r.splice(e,1);break}};e.documentElement.addEventListener(this.POINTER_UP,l,!1),e.documentElement.addEventListener(this.POINTER_CANCEL,l,!1),this._pointerDocumentListener=!0}return this},addPointerListenerMove:function(t,e,i,n){function o(t){if(t.pointerType!==t.MSPOINTER_TYPE_MOUSE&&"mouse"!==t.pointerType||0!==t.buttons){for(var e=0;e<a.length;e++)if(a[e].pointerId===t.pointerId){a[e]=t;break}t.touches=a.slice(),t.changedTouches=[t],i(t)}}var s="_leaflet_",a=this._pointers;return t[s+"touchmove"+n]=o,t.addEventListener(this.POINTER_MOVE,o,!1),this},addPointerListenerEnd:function(t,e,i,n){var o="_leaflet_",s=this._pointers,a=function(t){for(var e=0;e<s.length;e++)if(s[e].pointerId===t.pointerId){s.splice(e,1);break}t.touches=s.slice(),t.changedTouches=[t],i(t)};return t[o+"touchend"+n]=a,t.addEventListener(this.POINTER_UP,a,!1),t.addEventListener(this.POINTER_CANCEL,a,!1),this},removePointerListener:function(t,e,i){var n="_leaflet_",o=t[n+e+i];switch(e){case"touchstart":t.removeEventListener(this.POINTER_DOWN,o,!1);break;case"touchmove":t.removeEventListener(this.POINTER_MOVE,o,!1);break;case"touchend":t.removeEventListener(this.POINTER_UP,o,!1),t.removeEventListener(this.POINTER_CANCEL,o,!1)}return this}}),o.Map.mergeOptions({touchZoom:o.Browser.touch&&!o.Browser.android23,bounceAtZoomLimits:!0}),o.Map.TouchZoom=o.Handler.extend({addHooks:function(){o.DomEvent.on(this._map._container,"touchstart",this._onTouchStart,this)},removeHooks:function(){o.DomEvent.off(this._map._container,"touchstart",this._onTouchStart,this)},_onTouchStart:function(t){var i=this._map;if(t.touches&&2===t.touches.length&&!i._animatingZoom&&!this._zooming){var n=i.mouseEventToLayerPoint(t.touches[0]),s=i.mouseEventToLayerPoint(t.touches[1]),a=i._getCenterLayerPoint();this._startCenter=n.add(s)._divideBy(2),this._startDist=n.distanceTo(s),this._moved=!1,this._zooming=!0,this._centerOffset=a.subtract(this._startCenter),i._panAnim&&i._panAnim.stop(),o.DomEvent.on(e,"touchmove",this._onTouchMove,this).on(e,"touchend",this._onTouchEnd,this),o.DomEvent.preventDefault(t)}},_onTouchMove:function(t){var e=this._map;if(t.touches&&2===t.touches.length&&this._zooming){var i=e.mouseEventToLayerPoint(t.touches[0]),n=e.mouseEventToLayerPoint(t.touches[1]);this._scale=i.distanceTo(n)/this._startDist,this._delta=i._add(n)._divideBy(2)._subtract(this._startCenter),1!==this._scale&&(e.options.bounceAtZoomLimits||!(e.getZoom()===e.getMinZoom()&&this._scale<1||e.getZoom()===e.getMaxZoom()&&this._scale>1))&&(this._moved||(o.DomUtil.addClass(e._mapPane,"leaflet-touching"),e.fire("movestart").fire("zoomstart"),this._moved=!0),o.Util.cancelAnimFrame(this._animRequest),this._animRequest=o.Util.requestAnimFrame(this._updateOnMove,this,!0,this._map._container),o.DomEvent.preventDefault(t))}},_updateOnMove:function(){var t=this._map,e=this._getScaleOrigin(),i=t.layerPointToLatLng(e),n=t.getScaleZoom(this._scale);t._animateZoom(i,n,this._startCenter,this._scale,this._delta,!1,!0)},_onTouchEnd:function(){if(!this._moved||!this._zooming)return void(this._zooming=!1);var t=this._map;this._zooming=!1,o.DomUtil.removeClass(t._mapPane,"leaflet-touching"),o.Util.cancelAnimFrame(this._animRequest),o.DomEvent.off(e,"touchmove",this._onTouchMove).off(e,"touchend",this._onTouchEnd);var i=this._getScaleOrigin(),n=t.layerPointToLatLng(i),s=t.getZoom(),a=t.getScaleZoom(this._scale)-s,r=a>0?Math.ceil(a):Math.floor(a),h=t._limitZoom(s+r),l=t.getZoomScale(h)/this._scale;t._animateZoom(n,h,i,l)},_getScaleOrigin:function(){var t=this._centerOffset.subtract(this._delta).divideBy(this._scale);return this._startCenter.add(t)}}),o.Map.addInitHook("addHandler","touchZoom",o.Map.TouchZoom),o.Map.mergeOptions({tap:!0,tapTolerance:15}),o.Map.Tap=o.Handler.extend({addHooks:function(){o.DomEvent.on(this._map._container,"touchstart",this._onDown,this)},removeHooks:function(){o.DomEvent.off(this._map._container,"touchstart",this._onDown,this)},_onDown:function(t){if(t.touches){if(o.DomEvent.preventDefault(t),this._fireClick=!0,t.touches.length>1)return this._fireClick=!1,void clearTimeout(this._holdTimeout);var i=t.touches[0],n=i.target;this._startPos=this._newPos=new o.Point(i.clientX,i.clientY),n.tagName&&"a"===n.tagName.toLowerCase()&&o.DomUtil.addClass(n,"leaflet-active"),this._holdTimeout=setTimeout(o.bind(function(){this._isTapValid()&&(this._fireClick=!1,this._onUp(),this._simulateEvent("contextmenu",i))},this),1e3),o.DomEvent.on(e,"touchmove",this._onMove,this).on(e,"touchend",this._onUp,this)}},_onUp:function(t){if(clearTimeout(this._holdTimeout),o.DomEvent.off(e,"touchmove",this._onMove,this).off(e,"touchend",this._onUp,this),this._fireClick&&t&&t.changedTouches){var i=t.changedTouches[0],n=i.target;n&&n.tagName&&"a"===n.tagName.toLowerCase()&&o.DomUtil.removeClass(n,"leaflet-active"),this._isTapValid()&&this._simulateEvent("click",i)}},_isTapValid:function(){return this._newPos.distanceTo(this._startPos)<=this._map.options.tapTolerance},_onMove:function(t){var e=t.touches[0];this._newPos=new o.Point(e.clientX,e.clientY)},_simulateEvent:function(i,n){var o=e.createEvent("MouseEvents");o._simulated=!0,n.target._simulatedClick=!0,o.initMouseEvent(i,!0,!0,t,1,n.screenX,n.screenY,n.clientX,n.clientY,!1,!1,!1,!1,0,null),n.target.dispatchEvent(o)}}),o.Browser.touch&&!o.Browser.pointer&&o.Map.addInitHook("addHandler","tap",o.Map.Tap),o.Map.mergeOptions({boxZoom:!0}),o.Map.BoxZoom=o.Handler.extend({initialize:function(t){this._map=t,this._container=t._container,this._pane=t._panes.overlayPane,this._moved=!1},addHooks:function(){o.DomEvent.on(this._container,"mousedown",this._onMouseDown,this)},removeHooks:function(){o.DomEvent.off(this._container,"mousedown",this._onMouseDown),this._moved=!1},moved:function(){return this._moved},_onMouseDown:function(t){return this._moved=!1,!t.shiftKey||1!==t.which&&1!==t.button?!1:(o.DomUtil.disableTextSelection(),o.DomUtil.disableImageDrag(),this._startLayerPoint=this._map.mouseEventToLayerPoint(t),void o.DomEvent.on(e,"mousemove",this._onMouseMove,this).on(e,"mouseup",this._onMouseUp,this).on(e,"keydown",this._onKeyDown,this))},_onMouseMove:function(t){this._moved||(this._box=o.DomUtil.create("div","leaflet-zoom-box",this._pane),o.DomUtil.setPosition(this._box,this._startLayerPoint),this._container.style.cursor="crosshair",this._map.fire("boxzoomstart"));var e=this._startLayerPoint,i=this._box,n=this._map.mouseEventToLayerPoint(t),s=n.subtract(e),a=new o.Point(Math.min(n.x,e.x),Math.min(n.y,e.y));o.DomUtil.setPosition(i,a),this._moved=!0,i.style.width=Math.max(0,Math.abs(s.x)-4)+"px",i.style.height=Math.max(0,Math.abs(s.y)-4)+"px"},_finish:function(){this._moved&&(this._pane.removeChild(this._box),this._container.style.cursor=""),o.DomUtil.enableTextSelection(),o.DomUtil.enableImageDrag(),o.DomEvent.off(e,"mousemove",this._onMouseMove).off(e,"mouseup",this._onMouseUp).off(e,"keydown",this._onKeyDown)},_onMouseUp:function(t){this._finish();var e=this._map,i=e.mouseEventToLayerPoint(t);if(!this._startLayerPoint.equals(i)){var n=new o.LatLngBounds(e.layerPointToLatLng(this._startLayerPoint),e.layerPointToLatLng(i));e.fitBounds(n),e.fire("boxzoomend",{boxZoomBounds:n})}},_onKeyDown:function(t){27===t.keyCode&&this._finish()}}),o.Map.addInitHook("addHandler","boxZoom",o.Map.BoxZoom),o.Map.mergeOptions({keyboard:!0,keyboardPanOffset:80,keyboardZoomOffset:1}),o.Map.Keyboard=o.Handler.extend({keyCodes:{left:[37],right:[39],down:[40],up:[38],zoomIn:[187,107,61,171],zoomOut:[189,109,173]},initialize:function(t){this._map=t,this._setPanOffset(t.options.keyboardPanOffset),this._setZoomOffset(t.options.keyboardZoomOffset)},addHooks:function(){var t=this._map._container;-1===t.tabIndex&&(t.tabIndex="0"),o.DomEvent.on(t,"focus",this._onFocus,this).on(t,"blur",this._onBlur,this).on(t,"mousedown",this._onMouseDown,this),this._map.on("focus",this._addHooks,this).on("blur",this._removeHooks,this)},removeHooks:function(){this._removeHooks();var t=this._map._container;o.DomEvent.off(t,"focus",this._onFocus,this).off(t,"blur",this._onBlur,this).off(t,"mousedown",this._onMouseDown,this),this._map.off("focus",this._addHooks,this).off("blur",this._removeHooks,this)},_onMouseDown:function(){if(!this._focused){var i=e.body,n=e.documentElement,o=i.scrollTop||n.scrollTop,s=i.scrollLeft||n.scrollLeft;this._map._container.focus(),t.scrollTo(s,o)}},_onFocus:function(){this._focused=!0,this._map.fire("focus")},_onBlur:function(){this._focused=!1,this._map.fire("blur")},_setPanOffset:function(t){var e,i,n=this._panKeys={},o=this.keyCodes;for(e=0,i=o.left.length;i>e;e++)n[o.left[e]]=[-1*t,0];for(e=0,i=o.right.length;i>e;e++)n[o.right[e]]=[t,0];for(e=0,i=o.down.length;i>e;e++)n[o.down[e]]=[0,t];for(e=0,i=o.up.length;i>e;e++)n[o.up[e]]=[0,-1*t]},_setZoomOffset:function(t){var e,i,n=this._zoomKeys={},o=this.keyCodes;for(e=0,i=o.zoomIn.length;i>e;e++)n[o.zoomIn[e]]=t;for(e=0,i=o.zoomOut.length;i>e;e++)n[o.zoomOut[e]]=-t},_addHooks:function(){o.DomEvent.on(e,"keydown",this._onKeyDown,this)},_removeHooks:function(){o.DomEvent.off(e,"keydown",this._onKeyDown,this)},_onKeyDown:function(t){var e=t.keyCode,i=this._map;if(e in this._panKeys){if(i._panAnim&&i._panAnim._inProgress)return;i.panBy(this._panKeys[e]),i.options.maxBounds&&i.panInsideBounds(i.options.maxBounds)}else{if(!(e in this._zoomKeys))return;i.setZoom(i.getZoom()+this._zoomKeys[e])}o.DomEvent.stop(t)}}),o.Map.addInitHook("addHandler","keyboard",o.Map.Keyboard),o.Handler.MarkerDrag=o.Handler.extend({initialize:function(t){this._marker=t},addHooks:function(){var t=this._marker._icon;this._draggable||(this._draggable=new o.Draggable(t,t)),this._draggable.on("dragstart",this._onDragStart,this).on("drag",this._onDrag,this).on("dragend",this._onDragEnd,this),this._draggable.enable(),o.DomUtil.addClass(this._marker._icon,"leaflet-marker-draggable")},removeHooks:function(){this._draggable.off("dragstart",this._onDragStart,this).off("drag",this._onDrag,this).off("dragend",this._onDragEnd,this),this._draggable.disable(),o.DomUtil.removeClass(this._marker._icon,"leaflet-marker-draggable")},moved:function(){return this._draggable&&this._draggable._moved},_onDragStart:function(){this._marker.closePopup().fire("movestart").fire("dragstart")},_onDrag:function(){var t=this._marker,e=t._shadow,i=o.DomUtil.getPosition(t._icon),n=t._map.layerPointToLatLng(i);e&&o.DomUtil.setPosition(e,i),t._latlng=n,t.fire("move",{latlng:n}).fire("drag")},_onDragEnd:function(t){this._marker.fire("moveend").fire("dragend",t)}}),o.Control=o.Class.extend({options:{position:"topright"},initialize:function(t){o.setOptions(this,t)},getPosition:function(){return this.options.position},setPosition:function(t){var e=this._map;return e&&e.removeControl(this),this.options.position=t,e&&e.addControl(this),this},getContainer:function(){return this._container},addTo:function(t){this._map=t;var e=this._container=this.onAdd(t),i=this.getPosition(),n=t._controlCorners[i];return o.DomUtil.addClass(e,"leaflet-control"),-1!==i.indexOf("bottom")?n.insertBefore(e,n.firstChild):n.appendChild(e),this},removeFrom:function(t){var e=this.getPosition(),i=t._controlCorners[e];return i.removeChild(this._container),this._map=null,this.onRemove&&this.onRemove(t),this},_refocusOnMap:function(){this._map&&this._map.getContainer().focus()}}),o.control=function(t){return new o.Control(t)},o.Map.include({addControl:function(t){return t.addTo(this),this},removeControl:function(t){return t.removeFrom(this),this},_initControlPos:function(){function t(t,s){var a=i+t+" "+i+s;e[t+s]=o.DomUtil.create("div",a,n)}var e=this._controlCorners={},i="leaflet-",n=this._controlContainer=o.DomUtil.create("div",i+"control-container",this._container);t("top","left"),t("top","right"),t("bottom","left"),t("bottom","right")},_clearControlPos:function(){this._container.removeChild(this._controlContainer)}}),o.Control.Zoom=o.Control.extend({options:{position:"topleft",zoomInText:"+",zoomInTitle:"Zoom in",zoomOutText:"-",zoomOutTitle:"Zoom out"},onAdd:function(t){var e="leaflet-control-zoom",i=o.DomUtil.create("div",e+" leaflet-bar");return this._map=t,this._zoomInButton=this._createButton(this.options.zoomInText,this.options.zoomInTitle,e+"-in",i,this._zoomIn,this),this._zoomOutButton=this._createButton(this.options.zoomOutText,this.options.zoomOutTitle,e+"-out",i,this._zoomOut,this),this._updateDisabled(),t.on("zoomend zoomlevelschange",this._updateDisabled,this),i},onRemove:function(t){t.off("zoomend zoomlevelschange",this._updateDisabled,this)},_zoomIn:function(t){this._map.zoomIn(t.shiftKey?3:1)},_zoomOut:function(t){this._map.zoomOut(t.shiftKey?3:1)},_createButton:function(t,e,i,n,s,a){var r=o.DomUtil.create("a",i,n);r.innerHTML=t,r.href="#",r.title=e;var h=o.DomEvent.stopPropagation;return o.DomEvent.on(r,"click",h).on(r,"mousedown",h).on(r,"dblclick",h).on(r,"click",o.DomEvent.preventDefault).on(r,"click",s,a).on(r,"click",this._refocusOnMap,a),r},_updateDisabled:function(){var t=this._map,e="leaflet-disabled";o.DomUtil.removeClass(this._zoomInButton,e),o.DomUtil.removeClass(this._zoomOutButton,e),t._zoom===t.getMinZoom()&&o.DomUtil.addClass(this._zoomOutButton,e),t._zoom===t.getMaxZoom()&&o.DomUtil.addClass(this._zoomInButton,e)}}),o.Map.mergeOptions({zoomControl:!0}),o.Map.addInitHook(function(){this.options.zoomControl&&(this.zoomControl=new o.Control.Zoom,this.addControl(this.zoomControl))}),o.control.zoom=function(t){return new o.Control.Zoom(t)},o.Control.Attribution=o.Control.extend({options:{position:"bottomright",prefix:'<a href="http://leafletjs.com" title="A JS library for interactive maps">Leaflet</a>'},initialize:function(t){o.setOptions(this,t),this._attributions={}},onAdd:function(t){this._container=o.DomUtil.create("div","leaflet-control-attribution"),o.DomEvent.disableClickPropagation(this._container);for(var e in t._layers)t._layers[e].getAttribution&&this.addAttribution(t._layers[e].getAttribution());return t.on("layeradd",this._onLayerAdd,this).on("layerremove",this._onLayerRemove,this),this._update(),this._container},onRemove:function(t){t.off("layeradd",this._onLayerAdd).off("layerremove",this._onLayerRemove)},setPrefix:function(t){return this.options.prefix=t,this._update(),this},addAttribution:function(t){return t?(this._attributions[t]||(this._attributions[t]=0),this._attributions[t]++,this._update(),this):void 0},removeAttribution:function(t){return t?(this._attributions[t]&&(this._attributions[t]--,this._update()),this):void 0},_update:function(){if(this._map){var t=[];for(var e in this._attributions)this._attributions[e]&&t.push(e);var i=[];this.options.prefix&&i.push(this.options.prefix),t.length&&i.push(t.join(", ")),this._container.innerHTML=i.join(" | ")}},_onLayerAdd:function(t){t.layer.getAttribution&&this.addAttribution(t.layer.getAttribution())},_onLayerRemove:function(t){t.layer.getAttribution&&this.removeAttribution(t.layer.getAttribution())}}),o.Map.mergeOptions({attributionControl:!0}),o.Map.addInitHook(function(){this.options.attributionControl&&(this.attributionControl=(new o.Control.Attribution).addTo(this))}),o.control.attribution=function(t){return new o.Control.Attribution(t)},o.Control.Scale=o.Control.extend({options:{position:"bottomleft",maxWidth:100,metric:!0,imperial:!0,updateWhenIdle:!1},onAdd:function(t){this._map=t;var e="leaflet-control-scale",i=o.DomUtil.create("div",e),n=this.options;return this._addScales(n,e,i),t.on(n.updateWhenIdle?"moveend":"move",this._update,this),t.whenReady(this._update,this),i},onRemove:function(t){t.off(this.options.updateWhenIdle?"moveend":"move",this._update,this)},_addScales:function(t,e,i){t.metric&&(this._mScale=o.DomUtil.create("div",e+"-line",i)),t.imperial&&(this._iScale=o.DomUtil.create("div",e+"-line",i))},_update:function(){var t=this._map.getBounds(),e=t.getCenter().lat,i=6378137*Math.PI*Math.cos(e*Math.PI/180),n=i*(t.getNorthEast().lng-t.getSouthWest().lng)/180,o=this._map.getSize(),s=this.options,a=0;o.x>0&&(a=n*(s.maxWidth/o.x)),this._updateScales(s,a)},_updateScales:function(t,e){t.metric&&e&&this._updateMetric(e),t.imperial&&e&&this._updateImperial(e)},_updateMetric:function(t){var e=this._getRoundNum(t);this._mScale.style.width=this._getScaleWidth(e/t)+"px",this._mScale.innerHTML=1e3>e?e+" m":e/1e3+" km"},_updateImperial:function(t){var e,i,n,o=3.2808399*t,s=this._iScale;o>5280?(e=o/5280,i=this._getRoundNum(e),s.style.width=this._getScaleWidth(i/e)+"px",s.innerHTML=i+" mi"):(n=this._getRoundNum(o),s.style.width=this._getScaleWidth(n/o)+"px",s.innerHTML=n+" ft")},_getScaleWidth:function(t){return Math.round(this.options.maxWidth*t)-10},_getRoundNum:function(t){var e=Math.pow(10,(Math.floor(t)+"").length-1),i=t/e;return i=i>=10?10:i>=5?5:i>=3?3:i>=2?2:1,e*i}}),o.control.scale=function(t){return new o.Control.Scale(t)},o.Control.Layers=o.Control.extend({options:{collapsed:!0,position:"topright",autoZIndex:!0},initialize:function(t,e,i){o.setOptions(this,i),this._layers={},this._lastZIndex=0,this._handlingClick=!1;for(var n in t)this._addLayer(t[n],n);for(n in e)this._addLayer(e[n],n,!0)},onAdd:function(t){return this._initLayout(),this._update(),t.on("layeradd",this._onLayerChange,this).on("layerremove",this._onLayerChange,this),this._container},onRemove:function(t){t.off("layeradd",this._onLayerChange,this).off("layerremove",this._onLayerChange,this)},addBaseLayer:function(t,e){return this._addLayer(t,e),this._update(),this},addOverlay:function(t,e){return this._addLayer(t,e,!0),this._update(),this},removeLayer:function(t){var e=o.stamp(t);return delete this._layers[e],this._update(),this},_initLayout:function(){var t="leaflet-control-layers",e=this._container=o.DomUtil.create("div",t);e.setAttribute("aria-haspopup",!0),o.Browser.touch?o.DomEvent.on(e,"click",o.DomEvent.stopPropagation):o.DomEvent.disableClickPropagation(e).disableScrollPropagation(e);var i=this._form=o.DomUtil.create("form",t+"-list");if(this.options.collapsed){o.Browser.android||o.DomEvent.on(e,"mouseover",this._expand,this).on(e,"mouseout",this._collapse,this);var n=this._layersLink=o.DomUtil.create("a",t+"-toggle",e);n.href="#",n.title="Layers",o.Browser.touch?o.DomEvent.on(n,"click",o.DomEvent.stop).on(n,"click",this._expand,this):o.DomEvent.on(n,"focus",this._expand,this),o.DomEvent.on(i,"click",function(){setTimeout(o.bind(this._onInputClick,this),0)},this),this._map.on("click",this._collapse,this)}else this._expand();this._baseLayersList=o.DomUtil.create("div",t+"-base",i),this._separator=o.DomUtil.create("div",t+"-separator",i),this._overlaysList=o.DomUtil.create("div",t+"-overlays",i),e.appendChild(i)},_addLayer:function(t,e,i){var n=o.stamp(t);this._layers[n]={layer:t,name:e,overlay:i},this.options.autoZIndex&&t.setZIndex&&(this._lastZIndex++,t.setZIndex(this._lastZIndex))},_update:function(){if(this._container){this._baseLayersList.innerHTML="",this._overlaysList.innerHTML="";var t,e,i=!1,n=!1;for(t in this._layers)e=this._layers[t],this._addItem(e),n=n||e.overlay,i=i||!e.overlay;this._separator.style.display=n&&i?"":"none"}},_onLayerChange:function(t){var e=this._layers[o.stamp(t.layer)];if(e){this._handlingClick||this._update();var i=e.overlay?"layeradd"===t.type?"overlayadd":"overlayremove":"layeradd"===t.type?"baselayerchange":null;i&&this._map.fire(i,e)}},_createRadioElement:function(t,i){var n='<input type="radio" class="leaflet-control-layers-selector" name="'+t+'"';i&&(n+=' checked="checked"'),n+="/>";var o=e.createElement("div");return o.innerHTML=n,o.firstChild},_addItem:function(t){var i,n=e.createElement("label"),s=this._map.hasLayer(t.layer);t.overlay?(i=e.createElement("input"),i.type="checkbox",i.className="leaflet-control-layers-selector",i.defaultChecked=s):i=this._createRadioElement("leaflet-base-layers",s),i.layerId=o.stamp(t.layer),o.DomEvent.on(i,"click",this._onInputClick,this);var a=e.createElement("span");a.innerHTML=" "+t.name,n.appendChild(i),n.appendChild(a);var r=t.overlay?this._overlaysList:this._baseLayersList;return r.appendChild(n),n},_onInputClick:function(){var t,e,i,n=this._form.getElementsByTagName("input"),o=n.length;for(this._handlingClick=!0,t=0;o>t;t++)e=n[t],i=this._layers[e.layerId],e.checked&&!this._map.hasLayer(i.layer)?this._map.addLayer(i.layer):!e.checked&&this._map.hasLayer(i.layer)&&this._map.removeLayer(i.layer);this._handlingClick=!1,this._refocusOnMap()},_expand:function(){o.DomUtil.addClass(this._container,"leaflet-control-layers-expanded")},_collapse:function(){this._container.className=this._container.className.replace(" leaflet-control-layers-expanded","")}}),o.control.layers=function(t,e,i){return new o.Control.Layers(t,e,i)},o.PosAnimation=o.Class.extend({includes:o.Mixin.Events,run:function(t,e,i,n){this.stop(),this._el=t,this._inProgress=!0,this._newPos=e,this.fire("start"),t.style[o.DomUtil.TRANSITION]="all "+(i||.25)+"s cubic-bezier(0,0,"+(n||.5)+",1)",o.DomEvent.on(t,o.DomUtil.TRANSITION_END,this._onTransitionEnd,this),o.DomUtil.setPosition(t,e),o.Util.falseFn(t.offsetWidth),this._stepTimer=setInterval(o.bind(this._onStep,this),50)},stop:function(){this._inProgress&&(o.DomUtil.setPosition(this._el,this._getPos()),this._onTransitionEnd(),o.Util.falseFn(this._el.offsetWidth))},_onStep:function(){var t=this._getPos();return t?(this._el._leaflet_pos=t,void this.fire("step")):void this._onTransitionEnd()},_transformRe:/([-+]?(?:\d*\.)?\d+)\D*, ([-+]?(?:\d*\.)?\d+)\D*\)/,_getPos:function(){var e,i,n,s=this._el,a=t.getComputedStyle(s);if(o.Browser.any3d){if(n=a[o.DomUtil.TRANSFORM].match(this._transformRe),!n)return;e=parseFloat(n[1]),i=parseFloat(n[2])}else e=parseFloat(a.left),i=parseFloat(a.top);return new o.Point(e,i,!0)},_onTransitionEnd:function(){o.DomEvent.off(this._el,o.DomUtil.TRANSITION_END,this._onTransitionEnd,this),this._inProgress&&(this._inProgress=!1,this._el.style[o.DomUtil.TRANSITION]="",this._el._leaflet_pos=this._newPos,clearInterval(this._stepTimer),this.fire("step").fire("end"))}}),o.Map.include({setView:function(t,e,n){if(e=e===i?this._zoom:this._limitZoom(e),t=this._limitCenter(o.latLng(t),e,this.options.maxBounds),n=n||{},this._panAnim&&this._panAnim.stop(),this._loaded&&!n.reset&&n!==!0){n.animate!==i&&(n.zoom=o.extend({animate:n.animate},n.zoom),n.pan=o.extend({animate:n.animate},n.pan));var s=this._zoom!==e?this._tryAnimatedZoom&&this._tryAnimatedZoom(t,e,n.zoom):this._tryAnimatedPan(t,n.pan);if(s)return clearTimeout(this._sizeTimer),this}return this._resetView(t,e),this},panBy:function(t,e){if(t=o.point(t).round(),e=e||{},!t.x&&!t.y)return this;if(this._panAnim||(this._panAnim=new o.PosAnimation,this._panAnim.on({step:this._onPanTransitionStep,end:this._onPanTransitionEnd},this)),e.noMoveStart||this.fire("movestart"),e.animate!==!1){o.DomUtil.addClass(this._mapPane,"leaflet-pan-anim");var i=this._getMapPanePos().subtract(t);this._panAnim.run(this._mapPane,i,e.duration||.25,e.easeLinearity)}else this._rawPanBy(t),this.fire("move").fire("moveend");return this},_onPanTransitionStep:function(){this.fire("move")},_onPanTransitionEnd:function(){o.DomUtil.removeClass(this._mapPane,"leaflet-pan-anim"),this.fire("moveend")},_tryAnimatedPan:function(t,e){var i=this._getCenterOffset(t)._floor();return(e&&e.animate)===!0||this.getSize().contains(i)?(this.panBy(i,e),!0):!1}}),o.PosAnimation=o.DomUtil.TRANSITION?o.PosAnimation:o.PosAnimation.extend({run:function(t,e,i,n){this.stop(),this._el=t,this._inProgress=!0,this._duration=i||.25,this._easeOutPower=1/Math.max(n||.5,.2),this._startPos=o.DomUtil.getPosition(t),this._offset=e.subtract(this._startPos),this._startTime=+new Date,this.fire("start"),this._animate()},stop:function(){this._inProgress&&(this._step(),this._complete())},_animate:function(){this._animId=o.Util.requestAnimFrame(this._animate,this),this._step()},_step:function(){var t=+new Date-this._startTime,e=1e3*this._duration;e>t?this._runFrame(this._easeOut(t/e)):(this._runFrame(1),this._complete())},_runFrame:function(t){var e=this._startPos.add(this._offset.multiplyBy(t));o.DomUtil.setPosition(this._el,e),this.fire("step")},_complete:function(){o.Util.cancelAnimFrame(this._animId),this._inProgress=!1,this.fire("end")},_easeOut:function(t){return 1-Math.pow(1-t,this._easeOutPower)}}),o.Map.mergeOptions({zoomAnimation:!0,zoomAnimationThreshold:4}),o.DomUtil.TRANSITION&&o.Map.addInitHook(function(){this._zoomAnimated=this.options.zoomAnimation&&o.DomUtil.TRANSITION&&o.Browser.any3d&&!o.Browser.android23&&!o.Browser.mobileOpera,this._zoomAnimated&&o.DomEvent.on(this._mapPane,o.DomUtil.TRANSITION_END,this._catchTransitionEnd,this)}),o.Map.include(o.DomUtil.TRANSITION?{_catchTransitionEnd:function(t){this._animatingZoom&&t.propertyName.indexOf("transform")>=0&&this._onZoomTransitionEnd()},_nothingToAnimate:function(){return!this._container.getElementsByClassName("leaflet-zoom-animated").length},_tryAnimatedZoom:function(t,e,i){if(this._animatingZoom)return!0;if(i=i||{},!this._zoomAnimated||i.animate===!1||this._nothingToAnimate()||Math.abs(e-this._zoom)>this.options.zoomAnimationThreshold)return!1;var n=this.getZoomScale(e),o=this._getCenterOffset(t)._divideBy(1-1/n),s=this._getCenterLayerPoint()._add(o);return i.animate===!0||this.getSize().contains(o)?(this.fire("movestart").fire("zoomstart"),this._animateZoom(t,e,s,n,null,!0),!0):!1},_animateZoom:function(t,e,i,n,s,a,r){r||(this._animatingZoom=!0),o.DomUtil.addClass(this._mapPane,"leaflet-zoom-anim"),this._animateToCenter=t,this._animateToZoom=e,o.Draggable&&(o.Draggable._disabled=!0),o.Util.requestAnimFrame(function(){this.fire("zoomanim",{center:t,zoom:e,origin:i,scale:n,delta:s,backwards:a})},this)},_onZoomTransitionEnd:function(){this._animatingZoom=!1,o.DomUtil.removeClass(this._mapPane,"leaflet-zoom-anim"),this._resetView(this._animateToCenter,this._animateToZoom,!0,!0),o.Draggable&&(o.Draggable._disabled=!1)}}:{}),o.TileLayer.include({_animateZoom:function(t){this._animating||(this._animating=!0,this._prepareBgBuffer());var e=this._bgBuffer,i=o.DomUtil.TRANSFORM,n=t.delta?o.DomUtil.getTranslateString(t.delta):e.style[i],s=o.DomUtil.getScaleString(t.scale,t.origin);e.style[i]=t.backwards?s+" "+n:n+" "+s},_endZoomAnim:function(){var t=this._tileContainer,e=this._bgBuffer;t.style.visibility="",t.parentNode.appendChild(t),o.Util.falseFn(e.offsetWidth),this._animating=!1},_clearBgBuffer:function(){var t=this._map;!t||t._animatingZoom||t.touchZoom._zooming||(this._bgBuffer.innerHTML="",this._bgBuffer.style[o.DomUtil.TRANSFORM]="")},_prepareBgBuffer:function(){var t=this._tileContainer,e=this._bgBuffer,i=this._getLoadedTilesPercentage(e),n=this._getLoadedTilesPercentage(t);return e&&i>.5&&.5>n?(t.style.visibility="hidden",void this._stopLoadingImages(t)):(e.style.visibility="hidden",e.style[o.DomUtil.TRANSFORM]="",this._tileContainer=e,e=this._bgBuffer=t,this._stopLoadingImages(e),void clearTimeout(this._clearBgBufferTimer))},_getLoadedTilesPercentage:function(t){var e,i,n=t.getElementsByTagName("img"),o=0;for(e=0,i=n.length;i>e;e++)n[e].complete&&o++;return o/i},_stopLoadingImages:function(t){var e,i,n,s=Array.prototype.slice.call(t.getElementsByTagName("img"));for(e=0,i=s.length;i>e;e++)n=s[e],n.complete||(n.onload=o.Util.falseFn,n.onerror=o.Util.falseFn,n.src=o.Util.emptyImageUrl,n.parentNode.removeChild(n))}}),o.Map.include({_defaultLocateOptions:{watch:!1,setView:!1,maxZoom:1/0,timeout:1e4,maximumAge:0,enableHighAccuracy:!1},locate:function(t){if(t=this._locateOptions=o.extend(this._defaultLocateOptions,t),!navigator.geolocation)return this._handleGeolocationError({code:0,message:"Geolocation not supported."}),this;var e=o.bind(this._handleGeolocationResponse,this),i=o.bind(this._handleGeolocationError,this);return t.watch?this._locationWatchId=navigator.geolocation.watchPosition(e,i,t):navigator.geolocation.getCurrentPosition(e,i,t),this},stopLocate:function(){return navigator.geolocation&&navigator.geolocation.clearWatch(this._locationWatchId),this._locateOptions&&(this._locateOptions.setView=!1),this},_handleGeolocationError:function(t){var e=t.code,i=t.message||(1===e?"permission denied":2===e?"position unavailable":"timeout");this._locateOptions.setView&&!this._loaded&&this.fitWorld(),this.fire("locationerror",{code:e,message:"Geolocation error: "+i+"."})},_handleGeolocationResponse:function(t){var e=t.coords.latitude,i=t.coords.longitude,n=new o.LatLng(e,i),s=180*t.coords.accuracy/40075017,a=s/Math.cos(o.LatLng.DEG_TO_RAD*e),r=o.latLngBounds([e-s,i-a],[e+s,i+a]),h=this._locateOptions;if(h.setView){var l=Math.min(this.getBoundsZoom(r),h.maxZoom);this.setView(n,l)}var u={latlng:n,bounds:r,timestamp:t.timestamp};for(var c in t.coords)"number"==typeof t.coords[c]&&(u[c]=t.coords[c]);this.fire("locationfound",u)}})}(window,document);
var oWorkerProperties, oGeneralProperties, oRotationProperties;
var oViewProperties;
var oPageProperties={};
var oFileAges;
var oStatusMessageTimer;
var oMapObjects={};
var regexCache={};
var iNow=Math.floor(Date.parse(new Date()) / 1000);
var oStates={};
var isIE=navigator.appVersion.indexOf("MSIE") != -1;
var crawlX=0;
var crawlY=0;
var crawling=0;
function getSidebarWidth() {
return 0;
}
function date(format, timestamp) {
var that=this,
jsdate, f, formatChr = /\\?([a-z])/gi, formatChrCb,
_pad = function (n, c) {
if ((n = n + "").length < c) {
return new Array((++c) - n.length).join("0") + n;
} else {
return n;
}
},
txt_words = ["Sun", "Mon", "Tues", "Wednes", "Thurs", "Fri", "Satur",
"January", "February", "March", "April", "May", "June", "July",
"August", "September", "October", "November", "December"],
txt_ordin = {
1: "st",
2: "nd",
3: "rd",
21: "st",
22: "nd",
23: "rd",
31: "st"
};
formatChrCb = function (t, s) {
return f[t] ? f[t]() : s;
};
f = {
d: function () { // Day of month w/leading 0; 01..31
return _pad(f.j(), 2);
},
D: function () { // Shorthand day name; Mon...Sun
return f.l().slice(0, 3);
},
j: function () { // Day of month; 1..31
return jsdate.getDate();
},
l: function () { // Full day name; Monday...Sunday
return txt_words[f.w()] + 'day';
},
N: function () { // ISO-8601 day of week; 1[Mon]..7[Sun]
return f.w() || 7;
},
S: function () { // Ordinal suffix for day of month; st, nd, rd, th
return txt_ordin[f.j()] || 'th';
},
w: function () { // Day of week; 0[Sun]..6[Sat]
return jsdate.getDay();
},
z: function () { // Day of year; 0..365
var a=new Date(f.Y(), f.n() - 1, f.j()),
b = new Date(f.Y(), 0, 1);
return Math.round((a - b) / 864e5) + 1;
},
W: function () { // ISO-8601 week number
var a=new Date(f.Y(), f.n() - 1, f.j() - f.N() + 3),
b = new Date(a.getFullYear(), 0, 4);
return 1 + Math.round((a - b) / 864e5 / 7);
},
F: function () { // Full month name; January...December
return txt_words[6 + f.n()];
},
m: function () { // Month w/leading 0; 01...12
return _pad(f.n(), 2);
},
M: function () { // Shorthand month name; Jan...Dec
return f.F().slice(0, 3);
},
n: function () { // Month; 1...12
return jsdate.getMonth() + 1;
},
t: function () { // Days in month; 28...31
return (new Date(f.Y(), f.n(), 0)).getDate();
},
L: function () { // Is leap year?; 0 or 1
return new Date(f.Y(), 1, 29).getMonth() === 1 | 0;
},
o: function () { // ISO-8601 year
var n=f.n(), W = f.W(), Y = f.Y();
return Y + (n === 12 && W < 9 ? -1 : n === 1 && W > 9);
},
Y: function () { // Full year; e.g. 1980...2010
return jsdate.getFullYear();
},
y: function () { // Last two digits of year; 00...99
return (f.Y() + "").slice(-2);
},
a: function () { // am or pm
return jsdate.getHours() > 11 ? "pm" : "am";
},
A: function () { // AM or PM
return f.a().toUpperCase();
},
B: function () { // Swatch Internet time; 000..999
var H=jsdate.getUTCHours() * 36e2, // Hours
i = jsdate.getUTCMinutes() * 60, // Minutes
s = jsdate.getUTCSeconds(); // Seconds
return _pad(Math.floor((H + i + s + 36e2) / 86.4) % 1e3, 3);
},
g: function () { // 12-Hours; 1..12
return f.G() % 12 || 12;
},
G: function () { // 24-Hours; 0..23
return jsdate.getHours();
},
h: function () { // 12-Hours w/leading 0; 01..12
return _pad(f.g(), 2);
},
H: function () { // 24-Hours w/leading 0; 00..23
return _pad(f.G(), 2);
},
i: function () { // Minutes w/leading 0; 00..59
return _pad(jsdate.getMinutes(), 2);
},
s: function () { // Seconds w/leading 0; 00..59
return _pad(jsdate.getSeconds(), 2);
},
u: function () { // Microseconds; 000000-999000
return _pad(jsdate.getMilliseconds() * 1000, 6);
},
e: function () { // Timezone identifier; e.g. Atlantic/Azores, ...
throw 'Not supported (see source code of date() for timezone on how to add support)';
},
I: function () { // DST observed?; 0 or 1
var a=new Date(f.Y(), 0), // Jan 1
c = Date.UTC(f.Y(), 0), // Jan 1 UTC
b = new Date(f.Y(), 6), // Jul 1
d = Date.UTC(f.Y(), 6); // Jul 1 UTC
return 0 + ((a - c) !== (b - d));
},
O: function () { // Difference to GMT in hour format; e.g. +0200
var a=jsdate.getTimezoneOffset();
return (a > 0 ? "-" : "+") + _pad(Math.abs(a / 60 * 100), 4);
},
P: function () { // Difference to GMT w/colon; e.g. +02:00
var O=f.O();
return (O.substr(0, 3) + ":" + O.substr(3, 2));
},
T: function () { // Timezone abbreviation; e.g. EST, MDT, ...
return 'UTC';
},
Z: function () { // Timezone offset in seconds (-43200...50400)
return -jsdate.getTimezoneOffset() * 60;
},
c: function () { // ISO-8601 date.
return 'Y-m-d\\Th:i:sP'.replace(formatChr, formatChrCb);
},
r: function () { // RFC 2822
return 'D, d M Y H:i:s O'.replace(formatChr, formatChrCb);
},
U: function () { // Seconds since UNIX epoch
return jsdate.getTime() / 1000 | 0;
}
};
this.date = function (format, timestamp) {
that = this;
jsdate = (
(typeof timestamp === 'undefined') ? new Date() : // Not provided
(timestamp instanceof Date) ? new Date(timestamp) : // JS Date()
new Date(timestamp * 1000) // UNIX timestamp (auto-convert to int)
);
return format.replace(formatChr, formatChrCb);
};
return this.date(format, timestamp);
}
function updateWorkerCounter() {
var oWorkerCounter=document.getElementById('workerLastRunCounter');
if(oWorkerCounter) {
if(oWorkerProperties.last_run) {
oWorkerCounter.innerHTML = date(oGeneralProperties.date_format, oWorkerProperties.last_run);
}
}
oWorkerCounter = null;
return true;
}
function rotatePage() {
if(oRotationProperties.nextStepUrl !== '') {
if(oRotationProperties.rotationEnabled == true) {
window.open(oRotationProperties.nextStepUrl, "_self");
return true;
}
} else {
window.location.reload(true);
return true;
}
return false;
}
function rotationCountdown() {
if(oRotationProperties.rotationEnabled && oRotationProperties.rotationEnabled == true && oRotationProperties.nextStepTime && oRotationProperties.nextStepTime !== '') {
oRotationProperties.nextStepTime -= 1;
if(oRotationProperties.nextStepTime <= 0) {
return rotatePage();
} else {
var oRefCountHead=document.getElementById('refreshCounterHead');
if(oRefCountHead) {
oRefCountHead.innerHTML = oRotationProperties.nextStepTime;
oRefCountHead = null;
}
var oRefCount=document.getElementById('refreshCounter');
if(oRefCount) {
oRefCount.innerHTML = oRotationProperties.nextStepTime;
oRefCount = null;
}
}
}
return false;
}
function getUrlParam(name) {
var name2=name.replace('[', '\\[').replace(']', '\\]');
var regexS="[\\?&]"+name2+"=([^&#]*)";
var regex=new RegExp( regexS );
var results=regex.exec(window.location);
if(results === null) {
return '';
} else {
return results[1];
}
}
function makeuri(addparams) {
var tmp=window.location.href.split('?');
var base=tmp[0];
tmp = tmp[1].split('#');
tmp = tmp[0].split('&');
var len=tmp.length;
var params={};
var pair=null;
for(var i=0; i < tmp.length; i++) {
pair = tmp[i].split('=');
if(addparams[pair[0]] !== undefined && addparams[pair[0]] == null)
continue;
params[pair[0]] = pair[1];
}
for (var key in addparams) {
if(addparams[key] != null) {
params[key] = addparams[key];
}
}
var aparams=[];
for (var key in params) {
aparams.push(key + '=' + params[key]);
}
return base + '?' + aparams.join('&');
}
function setRotationLabel() {
if(oRotationProperties.rotationEnabled == true) {
document.getElementById('rotationStart').style.display = 'none';
document.getElementById('rotationStop').style.display = 'inline';
} else {
document.getElementById('rotationStart').style.display = 'inline';
document.getElementById('rotationStop').style.display = 'none';
}
}
function switchRotation() {
if(oRotationProperties.rotationEnabled == true) {
oRotationProperties.rotationEnabled = false;
setRotationLabel();
} else {
oRotationProperties.rotationEnabled = true;
setRotationLabel();
}
}
function getCurrentTime() {
var oDate=new Date();
var sHours=oDate.getHours();
sHours = (( sHours < 10) ? "0"+sHours : sHours);
var sMinutes=oDate.getMinutes();
sMinutes = (( sMinutes < 10) ? "0"+sMinutes : sMinutes);
var sSeconds=oDate.getSeconds();
sSeconds = (( sSeconds < 10) ? "0"+sSeconds : sSeconds);
return sHours+":"+sMinutes+":"+sSeconds;
}
function getRandomLowerCaseLetter() {
return String.fromCharCode(97 + Math.round(Math.random() * 25));
}
function getRandom(min, max) {
if( min > max ) {
return -1;
}
if( min == max ) {
return min;
}
return min + parseInt(Math.random() * (max-min+1), 0);
}
function pageWidth() {
var w;
if(window.innerWidth !== null  && typeof window.innerWidth !== 'undefined') {
w = window.innerWidth;
} else if(document.documentElement && document.documentElement.clientWidth) {
w = document.documentElement.clientWidth;
} else if(document.body !== null) {
w = document.body.clientWidth;
} else {
w = null;
}
return w;
}
function pageHeight() {
var h;
if(window.innerHeight !== null && typeof window.innerHeight !== 'undefined') {
h = window.innerHeight;
} else if(document.documentElement && document.documentElement.clientHeight) {
h = document.documentElement.clientHeight;
} else if(document.body !== null) {
h = document.body.clientHeight;
} else {
h = null;
}
return h;
}
function getScrollTop() {
if (typeof window.pageYOffset !== 'undefined')
return window.pageYOffset;
else if (typeof document.compatMode !== 'undefined' && document.compatMode !== 'BackCompat')
return document.documentElement.scrollTop;
else if (typeof document.body !== 'undefined')
return document.body.scrollTop;
}
function getScrollLeft() {
if (typeof window.pageXOffset !== 'undefined')
return window.pageXOffset;
else if (typeof document.compatMode != 'undefined' && document.compatMode !== 'BackCompat')
return document.documentElement.scrollLeft;
else if (typeof document.body !== 'undefined')
return document.body.scrollLeft;
}
function scrollSlow(iTargetX, iTargetY, iSpeed) {
var currentScrollTop=getScrollTop();
var currentScrollLeft=getScrollLeft();
var iMapOffsetTop;
var scrollTop;
var scrollLeft;
var iWidth;
var iHeight;
var iStep=10;
iTargetX = parseInt(iTargetX);
iTargetY = parseInt(iTargetY);
if((iTargetX !== crawlX || iTargetY !== crawlY) && crawlX !== 0 && crawlY !== 0) {
crawling = 1;
} else if(crawlX == 0 && crawlY == 0) {
crawlX = iTargetX;
crawlY = iTargetY;
}
var oMap=document.getElementById('map');
if(oMap && oMap.offsetTop) {
iMapOffsetTop = oMap.offsetTop;
} else {
iMapOffsetTop = 0;
}
oMap = null;
iWidth  = pageWidth();
iHeight = pageHeight() - iMapOffsetTop;
if((iTargetY < (currentScrollTop+iHeight/2+iStep) && iTargetY >= (currentScrollTop+iHeight/2-iStep)) || (currentScrollTop<iStep && iTargetY<iHeight/2)) {
scrollTop = 0;
} else if(iTargetY < (currentScrollTop+iHeight/2) && currentScrollTop>iStep) {
scrollTop = -iStep;
} else if(iTargetY > (currentScrollTop+iHeight/2)) {
scrollTop = iStep;
} else {
eventlog("js-error", "critical", "JS-Error occured: iTargetY: " +iTargetY);
scrollTop = 0;
}
if((iTargetX < (currentScrollLeft+iWidth/2+iStep) && iTargetX >= (currentScrollLeft+iWidth/2-iStep)) || (currentScrollLeft<iStep && iTargetX<iWidth/2)) {
scrollLeft = 0;
} else if(iTargetX < (currentScrollLeft+iWidth/2) && currentScrollLeft>iStep) {
scrollLeft = -iStep;
} else if(iTargetX > (currentScrollLeft+iWidth/2)) {
scrollLeft = iStep;
} else {
eventlog("js-error", "critical", "JS-Error occured: iTargetX: " +iTargetX);
scrollLeft = 0;
}
eventlog("scroll", "debug", currentScrollLeft+" to "+iTargetX+" = "+scrollLeft+", "+currentScrollTop+" to "+iTargetY+" = "+scrollTop);
if((scrollTop !== 0 || scrollLeft !== 0) && crawling == 0) {
window.scrollBy(scrollLeft, scrollTop);
if (currentScrollTop !== getScrollTop() || currentScrollLeft !== getScrollLeft()) {
setTimeout(function() { scrollSlow(iTargetX, iTargetY, iSpeed); }, iSpeed);
};
} else {
eventlog("scroll", "debug", 'No need to scroll: '+currentScrollLeft+' - '+iTargetX+', '+currentScrollTop+' - '+iTargetY);
crawlX=0;
crawlY=0;
crawling=0;
}
}
function escapeUrlValues(sStr) {
if(typeof sStr === undefined || sStr === null || sStr === '') {
return sStr;
}
sStr = new String(sStr);
if(sStr.search('\\+') !== -1) {
sStr = sStr.replace(/\+/g, '%2B');
}
if(sStr.search('&') !== -1) {
sStr = sStr.replace(/&/g, '%26');
}
if(sStr.search('#') !== -1) {
sStr = sStr.replace(/#/g, '%23');
}
if(sStr.search(':') !== -1) {
sStr = sStr.replace(/:/g, '%3A');
}
if(sStr.search(' ') !== -1) {
sStr = sStr.replace(/ /g, '%20');
}
if(sStr.search('=') !== -1) {
sStr = sStr.replace(/=/g, '%3D');
}
if(sStr.search('\\?') !== -1) {
sStr = sStr.replace(/\?/g, '%3F');
}
return sStr;
}
function oDump(object, depth, max){
depth = depth || 0;
max = max || 2;
if (depth > max) {
return false;
}
var indent="";
for (var i=0; i < depth; i++) {
indent += "  ";
}
var output="";
for (var key in object) {
output += "\n" + indent + key + ": ";
switch (typeof object[key]) {
case "object": output += oDump(object[key], depth + 1, max); break;
case "function": output += "function"; break;
default: output += object[key]; break;
}
}
return output;
}
function oLength(object) {
var c=0;
for(var key in object)
c++;
return c;
}
function isFirefox() {
return navigator.userAgent.indexOf("Firefox") > -1;
}
addDOMLoadEvent = (function(){
var load_events=[],
load_timer,
script,
done,
exec,
old_onload,
init = function () {
done = true;
clearInterval(load_timer);
while (exec = load_events.shift())
setTimeout(exec, 50);
if (script) script.onreadystatechange = '';
};
return function (func) {
if (done) return func();
if (!load_events[0]) {
if (document.addEventListener)
document.addEventListener("DOMContentLoaded", init, false);
/*@cc_on @*/
/*@if (@_win32)
document.write("<script id=__ie_onload defer src=><\/script>");
script = document.getElementById("__ie_onload");
script.onreadystatechange = function() {
if (this.readyState == "complete")
init(); // call the onload handler
};
@end
@*/
if (/KHTML|WebKit|iCab/i.test(navigator.userAgent)) { // sniff
load_timer = setInterval(function() {
if (/loaded|complete/.test(document.readyState))
init(); // call the onload handler
}, 10);
}
old_onload = window.onload;
window.onload = function() {
init();
if (old_onload) old_onload();
};
}
load_events.push(func);
}
})();
function handleJSError(sMsg, sUrl, iLine) {
if(!isset(sUrl))
var sUrl='<Empty URL>';
eventlog("js-error", "critical", "JS-Error occured: " + sMsg + " " + sUrl + " (" + iLine + ")");
frontendMessage({
'type'    : 'error',
'title'   : 'Error: Javascript Error',
'message' : 'Javascript error occured:\n ' + sMsg + ' '
+ sUrl + ' (' + iLine + ')'
});
return false;
}
function handleException(e) {
var msg=e.name+': '+e.message;
if (e.stack)
msg += '<br><code>'+e.stack+'</code>';
handleJSError(msg, e.fileName, e.lineNumber);
}
try {
window.onerror = handleJSError;
} catch(er) {}
function addEvent(obj, type, fn) {
if(obj.addEventListener) {
obj.addEventListener(type, fn, false);
} else if (obj.attachEvent) {
obj.attachEvent("on"+type, fn);
}
}
function removeEvent(obj, type, fn) {
if(obj.removeEventListener) {
obj.removeEventListener(type, fn, false);
} else if (obj.detachEvent) {
obj.detachEvent("on"+type, fn);
}
}
function preventDefaultEvents(event) {
if (event.preventDefault)
event.preventDefault();
else
event.returnValue = false;
if (event.stopPropagation)
event.stopPropagation();
return false;
}
function displayStatusMessage(msg, type, hold) {
var iMessageTime=5000;
var oMessage=document.getElementById('statusMessage');
if(!oMessage) {
oMessage = document.createElement('div');
oMessage.setAttribute('id', 'statusMessage');
if(isIE)
oMessage.style.filter = 'alpha(opacity=85)';
document.body.appendChild(oMessage);
}
if(oStatusMessageTimer) {
clearTimeout(oStatusMessageTimer);
}
var cont=msg;
if (type) {
cont = '<div class="'+type+'">'+cont+'</div>';
}
oMessage.innerHTML = cont;
oMessage.style.display = 'block';
if (type != 'loading') {
oMessage.onmousedown = function() { hideStatusMessage(); return true; };
}
if (!hold) {
oStatusMessageTimer = window.setTimeout(function() { hideStatusMessage(); }, iMessageTime);
}
oMessage = null;
}
function hideStatusMessage() {
var oMessage=document.getElementById('statusMessage');
if(oMessage) {
oMessage.style.display = 'none';
oMessage.onmousedown = null;
}
}
function renderNagVisTextbox(id, bgColor, borderColor, x, y, z, w, h, text, customStyle) {
var oLabelDiv=document.createElement('div');
oLabelDiv.setAttribute('id', id);
oLabelDiv.className = 'box';
oLabelDiv.style.background = bgColor;
oLabelDiv.style.borderColor = borderColor;
oLabelDiv.style.left = x + 'px';
oLabelDiv.style.top = y + 'px';
if(w && w !== '' && w !== 'auto')
oLabelDiv.style.width = addZoomFactor(w) + 'px';
if(h && h !== '' && h !== 'auto')
oLabelDiv.style.height = addZoomFactor(h) + 'px';
oLabelDiv.style.zIndex = parseInt(z) + 1;
if(borderColor == 'transparent')
oLabelDiv.style.borderStyle = 'none';
else
oLabelDiv.style.borderStyle = 'solid';
var oLabelSpan=null;
if(oLabelDiv.childNodes.length == 0)
oLabelSpan = document.createElement('span');
else
oLabelSpan = oLabelDiv.childNodes[0];
if(customStyle && customStyle !== '') {
var aStyle=customStyle.split(';');
for(var i in aStyle) {
if(typeof(aStyle[i]) !== 'string')
continue;
var aOpt=aStyle[i].split(':');
if(aOpt[0] && aOpt[0] != '' && aOpt[1] && aOpt[1] != '') {
var sKey=aOpt[0].replace(/(-[a-zA-Z])/g, '$1');
var regex=/(-[a-zA-Z])/;
var result=regex.exec(aOpt[0]);
if(result !== null) {
for (var i=1; i < result.length; i++) {
var fixed=result[i].replace('-', '').toUpperCase();
sKey = sKey.replace(result[i], fixed);
}
}
oLabelSpan.style[sKey] = aOpt[1];
}
aOpt = null;
}
aStyle = null;
}
oLabelSpan.innerHTML = text;
executeJS(oLabelSpan);
oLabelDiv.appendChild(oLabelSpan);
if (isZoomed()) {
oLabelDiv.width  = addZoomFactor(oLabelDiv.width);
oLabelDiv.height = addZoomFactor(oLabelDiv.height);
var fontSize=getEffectiveStyle(oLabelSpan, 'font-size');
if(fontSize === null) {
eventlog(
"renderNagVisTextbox",
"critical",
"Unable to fetch font-size attribute for textbox"
);
} else {
if (fontSize.indexOf('px') !== -1) {
var fontSize=parseFloat(fontSize.replace('px', ''));
oLabelSpan.style.fontSize = addZoomFactor(fontSize) + 'px';
} else {
eventlog(
"renderNagVisTextbox",
"critical",
"Zoom: Can not handle this font-size declaration (" + fontSize + ")"
);
}
}
}
oLabelSpan = null;
return oLabelDiv;
}
function lightenColor(code, rD, gD, bD) {
var r=parseInt(code.substring(1, 3), 16);
var g=parseInt(code.substring(3, 5), 16);
var b=parseInt(code.substring(5, 7), 16);
r += rD;  if (r > 255) r = 255;  if (r < 0) r = 0;
g += gD;  if (g > 255) g = 255;  if (g < 0) g = 0;
b += bD;  if (b > 255) b = 255;  if (b < 0) b = 0;
code  = r.length < 2 ? "0"+r.toString(16) : r.toString(16);
code += g.length < 2 ? "0"+g.toString(16) : g.toString(16);
code += b.length < 2 ? "0"+b.toString(16) : b.toString(16);
return "#" + code.toUpperCase();
}
function getRegEx(n, exp, mod) {
if(typeof(regexCache[n]) !== 'undefined')
return regexCache[n];
else
if(mod !== undefined) {
regexCache[n+'-'+mod] = new RegExp(exp, mod);
return regexCache[n+'-'+mod];
} else {
regexCache[n] = new RegExp(exp);
return regexCache[n];
}
}
function storeUserOption(key, value) {
oUserProperties[key] = value;
call_ajax(oGeneralProperties.path_server + '?mod=User&act=setOption&'
+'opts['+escapeUrlValues(key)+']='+escapeUrlValues(value), {
decode_json: false
});
}
function isset(v) {
return typeof(v) !== 'undefined' && v !== null;
}
function isInt(v) {
return parseFloat(v) == parseInt(v) && !isNaN(v);
}
function isFloat(v) {
return parseFloat(v) == v && !isNaN(v);
}
function pxToInt(v) {
return parseInt(v.replace('px', ''));
}
function isRelativeCoord(v) {
return isset(v) && ((!isInt(v) && !isFloat(v)) || v.length === 6);
}
Object.size = function(obj) {
var size=0, key;
for (key in obj) {
if (obj.hasOwnProperty(key)) size++;
}
return size;
}
if (!Function.prototype.bind) {
Function.prototype.bind = function(oThis) {
if (typeof this !== 'function') {
throw new TypeError('Function.prototype.bind - what is trying to be bound is not callable');
}
var aArgs=Array.prototype.slice.call(arguments, 1),
fToBind = this,
fNOP    = function() {},
fBound  = function() {
return fToBind.apply(this instanceof fNOP
? this
: oThis,
aArgs.concat(Array.prototype.slice.call(arguments)));
};
fNOP.prototype = this.prototype;
fBound.prototype = new fNOP();
return fBound;
};
}
if (!Array.prototype.indexOf) {
Array.prototype.indexOf = function(searchElement ) {
"use strict";
if (this === void 0 || this === null)
throw new TypeError();
var t=Object(this);
var len=t.length >>> 0;
if (len === 0)
return -1;
var n=0;
if (arguments.length > 0)
{
n = Number(arguments[1]);
if (n !== n)
n = 0;
else if (n !== 0 && n !== (1 / 0) && n !== -(1 / 0))
n = (n > 0 || -1) * Math.floor(Math.abs(n));
}
if (n >= len)
return -1;
var k=n >= 0
? n
: Math.max(len - Math.abs(n), 0);
for (; k < len; k++)
{
if (k in t && t[k] === searchElement)
return k;
}
return -1;
};
}
function getEffectiveStyle(e, attr) {
if(e.style[attr]) {
return e.style[attr];
} else if(document.defaultView && document.defaultView.getComputedStyle) {
return document.defaultView.getComputedStyle(e, null).getPropertyValue(attr);
} else if(e.currentStyle){
var ie_attr=attr.replace(/\-(\w)/g, function (strMatch, p1){
return p1.toUpperCase();
});
var f=e.currentStyle[ie_attr];
if(f.length > 0) {
return f;
}
}
return null;
}
var g_zoom_factor=null;
function getZoomFactor() {
if(g_zoom_factor !== null)
return g_zoom_factor; // only compute once
var zoom=getViewParam('zoom');
if (zoom === null || zoom == 'fill')
g_zoom_factor = 100;
else
g_zoom_factor = parseInt(zoom);
return g_zoom_factor;
}
function isZoomed() {
return getZoomFactor() !== 100;
}
function addZoomFactor(coord, forced) {
if (typeof(forced) === 'undefined')
var forced=false;
if (!forced && oGeneralProperties.zoom_scale_objects && oGeneralProperties.zoom_scale_objects != 1)
return parseInt(coord);
return parseInt(coord * getZoomFactor() / 100);
}
function rmZoomFactor(coord, forced) {
if (typeof(forced) === 'undefined')
var forced=false;
if (!forced && oGeneralProperties.zoom_scale_objects && oGeneralProperties.zoom_scale_objects != 1)
return parseInt(coord);
return parseInt(coord / getZoomFactor() * 100);
}
function zoomHandler(event, obj, forced_zoom) {
if(obj == window) {
if(event.srcElement) {
var obj=event.srcElement;
}
}
if(!obj)
return false;
obj.style.display = 'block';
var width=addZoomFactor(obj.width, forced_zoom);
var height=addZoomFactor(obj.height, forced_zoom);
obj.style.display = 'none';
obj.width  = width;
obj.height = height;
obj.style.display = 'block';
var arr=obj.id.split('-');
var map_obj=getMapObjByDomObjId(arr[0]);
if(map_obj && typeof(map_obj.updateLabel) == 'function') {
map_obj.updateLabel();
}
map_obj = null;
obj = null;
}
function addZoomHandler(oImage, forced_zoom) {
if(!isZoomed())
return; // If not zoomed, no handler is needed
if (typeof(forced_zoom) == 'undefined')
var forced_zoom=false;
oImage.style.display = 'none';
addEvent(oImage, 'load', function(event) { zoomHandler(event, this, forced_zoom); });
oImage = null;
}
function _(s, replace) {
if(typeof s === 'undefined')
return '';
if(isset(oLocales[s])) {
s = oLocales[s];
} else {
eventlog(
"localize",
"warning",
"String is not localizable '" + s + "'"
);
}
s = s.replace(/<(\/|)(i|b)>/ig, '');
s = s.replace('&auml;', 'ä').replace('&uuml;', 'ü');
s = s.replace('&ouml;', 'ö').replace('&szlig;', '');
if(typeof replace != "undefined") {
for(var i=0; i < replace.length; i++) {
s = s.replace("["+replace[i][0]+"]", replace[i][1]);
}
}
return s;
}
function has_class(o, cn) {
if (typeof o.className === 'undefined')
return false;
var parts=o.className.split(' ');
for (var x=0; x < parts.length; x++) {
if (parts[x] == cn)
return true;
}
return false;
}
function remove_class(o, cn) {
var parts=o.className.split(' ');
var new_parts=Array();
for (var x=0; x < parts.length; x++) {
if (parts[x] != cn)
new_parts.push(parts[x]);
}
o.className = new_parts.join(" ");
}
function add_class(o, cn) {
if (!has_class(o, cn))
o.className += " " + cn;
}
function change_class(o, a, b) {
remove_class(o, a);
add_class(o, b);
}
function middle(x1, x2, cut) {
return parseInt(x1) + parseInt((x2 - x1) * cut);
}
function max(arr) {
var max=arr[0];
for (var i=1, len = arr.length; i < len; i++) {
if (arr[i] > max) {
max = arr[i];
}
}
return max;
}
function min(arr) {
var min=arr[0];
for (var i=1, len = arr.length; i < len; i++) {
if (arr[i] < min) {
min = arr[i];
}
}
return min;
}
function newX(a, b, x, y) {
return Math.round(Math.cos(Math.atan2(y,x)+Math.atan2(b,a))*Math.sqrt(x*x+y*y));
}
function newY(a, b, x, y) {
return Math.round(Math.sin(Math.atan2(y,x)+Math.atan2(b,a))*Math.sqrt(x*x+y*y));
}
function merge_args() {
var defaults=arguments[0];
var args=arguments[1] || {};
for (var name in args)
defaults[name] = args[name];
return defaults;
}
function executeJS(obj) {
var aScripts=obj.getElementsByTagName('script');
for (var i=0; i < aScripts.length; i++) {
if (aScripts[i].src && aScripts[i].src !== '') {
var oScr=document.createElement('script');
oScr.src = aScripts[i].src;
document.getElementsByTagName("HEAD")[0].appendChild(oScr);
} else {
try {
eval(aScripts[i].text);
} catch(e) {
alert(aScripts[i].text + "\nError:" + e.message);
}
}
}
}
function getTargetRaw(event) {
return event.target ? event.target : event.srcElement;
}
function getTargetByClass(event, className) {
var target=getTargetRaw(event);
while (target && !has_class(target, className))
target = target.parentNode;
return target;
}
function toggleMapObjectLock(event, object_id) {
g_view.toggleObjectLock(object_id);
return preventDefaultEvents(event);
}
function toggleAllMapObjectsLock(event) {
var lock=g_view.hasUnlocked();
for (var object_id in g_view.objects)
g_view.toggleObjectLock(object_id, lock);
if (!lock)
storeUserOption('unlocked-' + oPageProperties.map_name, '*');
else
storeUserOption('unlocked-' + oPageProperties.map_name, '');
return preventDefaultEvents(event);
}
var draggingEnabled=true;
var draggingObject=null;
var dragObjectOffset=null;
var dragObjectPos=null;
var dragObjectStartPos=null;
var dragObjectChilds={};
var dragStopHandlers={};
var dragMoveHandlers={};
var dragObjects={};
var g_resize_obj=null; //This gets a value as soon as a resize start
function g_resize_object() {
this.el        = null; //pointer to the object
this.dir    = "";      //type of current resize (n, s, e, w, ne, nw, se, sw)
this.grabx = null;     //Some useful values
this.graby = null;
this.width = null;
this.height = null;
this.left = null;
this.top = null;
}
function getDirection(event, el) {
var xPos, yPos, offset, dir;
dir = "";
xPos = event.layerX ? event.layerX : event.offsetX ? event.offsetX : 0;
yPos = event.layerY ? event.layerY : event.offsetY ? event.offsetY : 0;
offset = 8;
if (yPos < offset) {
dir += "n";
}	else if (yPos > el.offsetHeight - offset) {
dir += "s";
}
if(xPos < offset) {
dir += "w";
}	else if (xPos > el.offsetWidth - offset) {
dir += "e";
}
return dir;
}
function resizeMouseDown(event) {
event = event || window.event;
var target=getTargetByClass(event, 'resizeable');
if (!target || target.id == '')
return true;
var dir=getDirection(event, target);
if (dir == "")
return true;
draggingEnabled = false;
draggingObject = null;
g_resize_obj = new g_resize_object();
g_resize_obj.el = target;
g_resize_obj.dir = dir;
g_resize_obj.grabx  = event.clientX;
g_resize_obj.graby  = event.clientY;
g_resize_obj.width  = target.offsetWidth;
g_resize_obj.height = target.offsetHeight;
g_resize_obj.left   = pxToInt(target.style.left);
g_resize_obj.top    = pxToInt(target.style.top);
return preventDefaultEvents(event);
}
function resizeMouseUp(event) {
event = event || window.event;
if (g_resize_obj === null)
return true;
draggingEnabled = true;
draggingObject = null;
var dom_obj=g_resize_obj.el;
var objId=dom_obj.id.split('-')[0];
var objX=rmZoomFactor(pxToInt(dom_obj.style.left), true);
var objY=rmZoomFactor(pxToInt(dom_obj.style.top), true);
var objW=rmZoomFactor(parseInt(dom_obj.style.width));
var objH=rmZoomFactor(parseInt(dom_obj.style.height));
var obj=getMapObjByDomObjId(objId);
obj.conf.x = objX;
obj.conf.y = objY;
obj.conf.w = objW;
obj.conf.h = objH;
obj.place();
if (!isInt(objX) || !isInt(objY) || !isInt(objW) || !isInt(objH)) {
alert('ERROR: Invalid coords ('+objX+'/'+objY+'/'+objW+'/'+objH+'). Terminating.');
return false;
}
var parts=g_view.unproject(objX, objY);
objX = parts[0];
objY = parts[1];
saveObjectAttr(objId, {
'x': objX,
'y': objY,
'w': objW,
'h': objH
});
g_resize_obj = null;
return preventDefaultEvents(event);
}
function resizeMouseMove(event) {
event = event || window.event;
var target=getTargetByClass(event, 'resizeable');
if (target) {
var str=getDirection(event, target);
if (str == "")
str = "";
else
str += "-resize";
target.style.cursor = str;
}
if (g_resize_obj === null)
return true;
var xMin=8, // The smallest width and height possible
yMin = 8;
if(g_resize_obj.dir.indexOf("e") != -1)
g_resize_obj.el.style.width = Math.max(xMin, g_resize_obj.width + event.clientX - g_resize_obj.grabx) + "px";
if(g_resize_obj.dir.indexOf("s") != -1) {
g_resize_obj.el.style.height = Math.max(yMin, g_resize_obj.height + event.clientY - g_resize_obj.graby) + "px";
}
if(g_resize_obj.dir.indexOf("w") != -1) {
g_resize_obj.el.style.left = Math.min(g_resize_obj.left + event.clientX - g_resize_obj.grabx, g_resize_obj.left + g_resize_obj.width - xMin) + "px";
g_resize_obj.el.style.width = Math.max(xMin, g_resize_obj.width - event.clientX + g_resize_obj.grabx) + "px";
}
if(g_resize_obj.dir.indexOf("n") != -1) {
g_resize_obj.el.style.top = Math.min(g_resize_obj.top + event.clientY - g_resize_obj.graby, g_resize_obj.top + g_resize_obj.height - yMin) + "px";
g_resize_obj.el.style.height = Math.max(yMin, g_resize_obj.height - event.clientY + g_resize_obj.graby) + "px";
}
return preventDefaultEvents(event);
}
function makeResizeable(trigger_obj) {
add_class(trigger_obj, 'resizeable');
addEvent(trigger_obj, 'mousedown', resizeMouseDown);
addEvent(trigger_obj, 'mouseup', resizeMouseUp);
}
function makeUnresizeable(trigger_obj) {
trigger_obj.style.cursor = '';
remove_class(trigger_obj, 'resizeable');
removeEvent(trigger_obj, 'mousedown', resizeMouseDown);
removeEvent(trigger_obj, 'mouseup', resizeMouseUp);
}
function getButton(event) {
if (event.which == null)
return (event.button < 2) ? "LEFT" : ((event.button == 4) ? "MIDDLE" : "RIGHT");
else
return (event.which < 2) ? "LEFT" : ((event.which == 2) ? "MIDDLE" : "RIGHT");
}
function makeUndragable(trigger_obj) {
delete dragStopHandlers[trigger_obj.id];
delete dragMoveHandlers[trigger_obj.id];
delete dragObjects[trigger_obj.id];
remove_class(trigger_obj, 'dragger');
removeEvent(trigger_obj, 'mousedown', dragStart);
removeEvent(document, 'mouseup', dragStop);
}
function makeDragable(trigger_obj, obj, dragStopHandler, dragMoveHandler) {
dragStopHandlers[trigger_obj.id] = dragStopHandler;
dragMoveHandlers[trigger_obj.id] = dragMoveHandler;
dragObjects[trigger_obj.id] = obj;
add_class(trigger_obj, 'dragger');
addEvent(trigger_obj, "mousedown", dragStart);
addEvent(document, "mouseup", dragStop);
}
function dragStart(event) {
event = event || window.event;
var target=getTargetByClass(event, 'dragger');
var button=getButton(event);
if (draggingObject !== null || button != 'LEFT' || !target || !draggingEnabled)
return true;
contextHide();
var parts=getEventMousePos(event),
posx  = parts[0],
posy  = parts[1];
draggingObject = target;
draggingObject.x = rmZoomFactor(pxToInt(draggingObject.style.left), true);
draggingObject.y = rmZoomFactor(pxToInt(draggingObject.style.top), true);
dragObjectOffset   = [ posx - draggingObject.x, posy - draggingObject.y ];
dragObjectStartPos = [ draggingObject.x, draggingObject.y ];
var sLabelName=target.id.replace('box_', 'rel_label_');
var oLabel=document.getElementById(sLabelName);
if(oLabel) {
dragObjectChilds[sLabelName] = [ oLabel.offsetLeft - draggingObject.x,
oLabel.offsetTop - draggingObject.y ];
}
return preventDefaultEvents(event);
}
function dragObject(event) {
event = event || window.event;
if (draggingObject === null || !draggingEnabled)
return true;
var parts=getEventMousePos(event),
posx  = parts[0],
posy  = parts[1],
newLeft = posx - dragObjectOffset[0],
newTop  = posy - dragObjectOffset[1];
if (typeof posx === 'undefined' || typeof posy === undefined)
return preventDefaultEvents(event);
draggingObject.style.position = 'absolute';
draggingObject.style.left = addZoomFactor(newLeft) + 'px';
draggingObject.style.top  = addZoomFactor(newTop) + 'px';
draggingObject.x = newLeft;
draggingObject.y = newTop;
moveRelativeObject(draggingObject.id, newTop, newLeft);
var idParts=draggingObject.id.split('-');
var obj=g_view.objects[idParts[0]];
if (obj.conf.view_type === 'line') {
var anchorId=idParts[2];
var parents=obj.getParentObjectIds(anchorId);
} else {
var parents=obj.getParentObjectIds();
}
var isRel=Object.keys(parents).length > 0;
for(var i in g_view.objects)
g_view.objects[i].highlight(false);
for (var objectId in parents)
g_view.objects[objectId].highlight(true);
var msg=null;
if(event.ctrlKey) {
var o=getNearestObject(draggingObject, newLeft, newTop)
if(o) {
o.highlight(true);
o = null;
}
if (!isRel)
msg = 'Hold CTRL till drop for relative positioning';
}
else if (event.shiftKey) {
for(var i in g_view.objects)
g_view.objects[i].highlight(false);
if (isRel)
msg = 'Hold SHIFT till drop for absolute positioning';
} else {
if (isRel)
msg = 'Press SHIFT for absolute positioning';
else
msg = 'Press CTRL for relative positioning';
}
if (msg !== null)
displayStatusMessage(msg, 'notice', true);
if(dragMoveHandlers[draggingObject.id])
dragMoveHandlers[draggingObject.id](draggingObject,
dragObjects[draggingObject.id], event);
return preventDefaultEvents(event);
}
function getNearestObject(draggingObject, x, y) {
var nearest=null;
var min=null;
var dist;
var obj;
for(var i in g_view.objects) {
obj = g_view.objects[i];
if(draggingObject.id.split('-')[0] == obj.conf.object_id)
continue;
if(obj.conf.view_type !== 'icon' || obj.conf.type == 'line')
continue;
var objX=obj.parseCoord(obj.conf.x, 'x');
var objY=obj.parseCoord(obj.conf.y, 'y');
dist = Math.sqrt(((objX - x) * (objX - x)) + ((objY - y) * (objY - y)));
if(min === null || dist < min) {
if(coordsReferTo(obj, draggingObject.id.split('-')[0])) {
continue;
}
min     = dist;
nearest = obj;
}
}
obj     = null;
min     = null;
dist    = null;
return nearest;
}
function coordsReferTo(obj, target_object_id) {
if (obj.conf.object_id == target_object_id) {
return true;
}
if (isRelativeCoord(obj.conf.x)) {
var xParent=getMapObjByDomObjId(obj.getCoordParent(obj.conf.x, -1));
if(coordsReferTo(xParent, target_object_id)) {
return true;
}
}
if (isRelativeCoord(obj.conf.y)) {
var yParent=getMapObjByDomObjId(obj.getCoordParent(obj.conf.y, -1));
if(coordsReferTo(yParent, target_object_id)) {
return true;
}
}
return false;
}
function moveRelativeObject(parentId, parentTop, parentLeft) {
var sLabelName=parentId.replace('box_', 'rel_label_');
if(typeof dragObjectChilds[sLabelName] !== 'undefined') {
var oLabel=document.getElementById(sLabelName);
if(oLabel) {
oLabel.style.position = 'absolute';
oLabel.style.left = (dragObjectChilds[sLabelName][0] + parentLeft) + 'px';
oLabel.style.top  = (dragObjectChilds[sLabelName][1] + parentTop) + 'px';
oLabel = null;
}
}
sLabelName = null;
}
function dragStop(event) {
if(draggingObject === null || !draggingEnabled
|| typeof draggingObject.y == 'undefined' || typeof draggingObject.x == 'undefined')
return;
hideStatusMessage();
if(draggingObject.y < 0 || draggingObject.x < 0) {
draggingObject.style.left = dragObjectStartPos[0] + 'px';
draggingObject.style.top  = dragObjectStartPos[1] + 'px';
draggingObject.x = dragObjectStartPos[0];
draggingObject.y = dragObjectStartPos[1];
moveRelativeObject(draggingObject.id, dragObjectStartPos[1], dragObjectStartPos[0]);
if(dragMoveHandlers[draggingObject.id])
dragMoveHandlers[draggingObject.id](draggingObject, dragObjects[draggingObject.id], event);
draggingObject = null;
return;
}
if(draggingObject.y == dragObjectStartPos[1] && draggingObject.x == dragObjectStartPos[0]) {
draggingObject = null;
return;
}
var oParent=null;
if(event.ctrlKey) {
var oParent=getNearestObject(draggingObject, draggingObject.x, draggingObject.y);
if(oParent)
oParent.highlight(false);
}
if(event.shiftKey)
oParent = false;
for(var objectId in getMapObjByDomObjId(draggingObject.id.split('-')[0]).getParentObjectIds())
getMapObjByDomObjId(objectId).highlight(false);
dragStopHandlers[draggingObject.id](draggingObject, dragObjects[draggingObject.id], oParent);
oParent = null;
draggingObject    = null;
}
function dragging() {
return draggingObject !== null;
}
var addObjType=null,
addViewType = null,
addNumLeft  = null,
addAction   = null,
addX        = [],
addY        = [],
addFollow   = false,
addShape    = null,
cloneId     = null;
function cloneObject(e, objId) {
cloneId = objId;
var obj=getMapObjByDomObjId(objId);
var numClicks=1;
if(obj.conf.type == 'textbox'|| obj.conf.type == 'container' || obj.conf.view_type == 'line' || obj.type == 'line')
numClicks = 2;
return addObject(e, obj.conf.type, obj.conf.view_type, numClicks, 'clone');
}
function addObject(event, objType, viewType, numLeft, action) {
event = event || window.event;
addObjType  = objType;
addViewType = viewType;
addNumLeft  = numLeft;
addAction   = action;
add_class(document.body, 'add');
return preventDefaultEvents(event);
}
function getEventMousePos(event) {
event = event || window.event;
if(getButton(event) != 'LEFT')
return null;
if(event.target) {
var target=event.target;
while(target) {
if(target.id && target.id == 'header') {
return false;
}
target = target.parentNode;
}
}
var posx, posy;
if (event.pageX || event.pageY) {
posx = event.pageX;
posy = event.pageY;
} else if (event.clientX || event.clientY) {
posx = event.clientX;
posy = event.clientY;
}
posy -= getHeaderHeight();
posx = rmZoomFactor(posx, true);
posy = rmZoomFactor(posy, true);
return [ posx, posy ];
}
function stopAdding() {
remove_class(document.body, 'add');
addObjType  = null,
addViewType = null,
addNumLeft  = null,
addAction   = null,
addX        = [],
addY        = [],
addFollow   = false,
addShape    = null;
}
function addClick(e) {
if(!adding())
return true;
var pos=getEventMousePos(e);
if (pos === false) {
stopAdding();
return false;
}
addX.push(pos[0] - getSidebarWidth());
addY.push(pos[1]);
addNumLeft -= 1;
pos = null;
if((addViewType === 'line' || addObjType === 'textbox' || addObjType === 'container' || addObjType === 'line')
&& addShape === null) {
addShape = new jsGraphics('map');
addShape.cnv.setAttribute('id', 'drawing');
addShape.setColor('#06B606');
addShape.setStroke(1);
addFollow = true;
}
if(addNumLeft > 0)
return false;
if(addObjType == 'textbox' || addObjType == 'container') {
var w=addX.pop() - addX[0];
var h=addY.pop() - addY[0];
}
var parts=g_view.unproject(addX, addY);
addX = parts[0];
addY = parts[1];
var sUrl='';
if(addAction == 'add' || addAction == 'clone')
sUrl = oGeneralProperties.path_server + '?mod=Map&act=addModify'
+ '&show=' + oPageProperties.map_name
+ '&type=' + addObjType
+ '&x=' + addX.join(',')
+ '&y=' + addY.join(',');
if(addObjType != 'textbox' && addObjType != 'container'
&& addObjType != 'shape' && addViewType != 'icon' && addViewType != '')
sUrl += '&view_type=' + addViewType;
if(addAction == 'clone' && cloneId !== null)
sUrl += '&clone_id=' + cloneId;
if(addObjType == 'textbox' || addObjType == 'container')
sUrl += '&w=' + w+ '&h=' + h;
if(sUrl === '')
return false;
if(addShape !== null) {
addShape.clear();
document.getElementById('map').removeChild(addShape.cnv);
}
showFrontendDialog(sUrl, _('Create Object'));
stopAdding();
return false;
}
function adding() {
return addNumLeft !== null;
}
function addFollowing(e) {
if(!addFollow)
return true;
var pos=getEventMousePos(e);
var start_x=addZoomFactor(addX[0]),
start_y = addZoomFactor(addY[0]);
var end_x=addZoomFactor(pos[0]),
end_y = addZoomFactor(pos[1]);
addShape.clear();
if(addViewType === 'line' || addObjType === 'line')
addShape.drawLine(start_x, start_y, end_x - getSidebarWidth(), end_y);
else
addShape.drawRect(start_x, start_y, (end_x - getSidebarWidth() - start_x),
(end_y - start_y));
addShape.paint();
}
function useGrid() {
return oViewProperties.grid_show === 1;
}
function gridParse() {
if (!useGrid())
return;
var oGrid=document.getElementById('grid');
if (!oGrid) {
var oGrid=document.createElement('div');
oGrid.setAttribute('id', 'grid');
document.getElementById('map').appendChild(oGrid);
}
else {
while (oGrid.firstChild) {
oGrid.removeChild(oGrid.firstChild);
}
}
var line=document.createElement('div');
line.style.backgroundColor = oViewProperties.grid_color;
var gridStep=addZoomFactor(oViewProperties.grid_steps);
var gridYStart=0;
var gridXStart=0;
var gridYEnd=pageHeight() - getHeaderHeight();
var gridXEnd=pageWidth();
var vline=null;
for(var gridX=gridStep; gridX < gridXEnd; gridX = gridX + gridStep) {
vline = line.cloneNode();
vline.className = "vertical";
vline.style.left   = gridX + 'px';
vline.style.top    = gridYStart + 'px';
vline.style.bottom = 0;
oGrid.appendChild(vline);
}
var hline;
for(var gridY=gridStep; gridY < gridYEnd; gridY = gridY + gridStep) {
hline = line.cloneNode();
hline.className = "horizontal";
hline.style.top    = gridY +'px';
hline.style.left   = gridXStart + 'px';
hline.style.right  = 0;
oGrid.appendChild(hline);
}
addEvent(window, "resize", gridRedraw);
addEvent(window, "scroll", gridRedraw);
}
function gridRemove() {
var oGrid=document.getElementById('grid');
if (oGrid)
oGrid.parentNode.removeChild(oGrid);
removeEvent(window, "resize", gridRedraw);
removeEvent(window, "scroll", gridRedraw);
}
function gridRedraw() {
gridRemove();
gridParse();
}
function gridToggle() {
if(useGrid()) {
oViewProperties.grid_show = 0;
gridRemove();
} else {
oViewProperties.grid_show = 1;
gridParse();
}
call_ajax(oGeneralProperties.path_server+'?mod=Map&act=modifyObject&map='
+ oPageProperties.map_name+'&type=global&id=0&grid_show='+oViewProperties.grid_show);
}
function coordsToGrid(x, y) {
x = "" + x;
y = "" + y;
if(x.indexOf(',') !== -1) {
x = x.split(',');
y = y.split(',');
for(var i=0; i < x.length; i++) {
x[i] = x[i] - (x[i] % addZoomFactor(oViewProperties.grid_steps));
y[i] = y[i] - (y[i] % addZoomFactor(ooViewProperties.grid_steps));
}
return [ x.join(','), y.join(',') ];
} else {
x = +x;
y = +y;
var gridMoveX=x - (x % addZoomFactor(oViewProperties.grid_steps));
var gridMoveY=y - (y % addZoomFactor(oViewProperties.grid_steps));
return [ gridMoveX, gridMoveY ];
}
}
function toggle_section(sec) {
var sections=document.getElementsByClassName('section');
for (var i=0; i < sections.length; i++) {
if (sections[i].id == 'sec_' + sec)
sections[i].style.display = '';
else
sections[i].style.display = 'none';
}
var nav_items=document.getElementById('nav').childNodes;
for (var i=0; i < nav_items.length; i++) {
if (nav_items[i].id == 'nav_' + sec)
add_class(nav_items[i], 'active');
else
remove_class(nav_items[i], 'active');
}
document.getElementById('sec').value = sec;
}
function toggle_option(name) {
var field=document.getElementById(name);
var txt=document.getElementById('_txt_' + name);
if(field && txt) {
if(field.style.display === 'none') {
field.style.display = '';
txt.style.display = 'none';
} else {
field.style.display = 'none';
txt.style.display = '';
}
txt = null;
field = null;
}
}
function togglePicker(id, state) {
var o=document.getElementById(id);
if(jscolor.picker && jscolor.picker.owner == o.color)
o.color.hidePicker();
else
o.color.showPicker();
o = null;
}
function pickWindowSize(id, dimension) {
var o=document.getElementById(id);
if(dimension == 'width') {
o.value = pageWidth();
} else {
o.value = pageHeight() - getHeaderHeight();
}
o = null;
}
function updateUserRoles(bAdd) {
var user_roles=document.getElementById('user_roles');
var available=document.getElementById('roles_available');
var selected=document.getElementById('roles_selected');
if (bAdd) {
var source=available;
var target=selected;
} else {
var source=selected;
var target=available;
}
if (source.selectedIndex == -1)
return false;
var optName=source.options[source.selectedIndex].text;
var optValue=source.options[source.selectedIndex].value;
source.options.remove(source.selectedIndex);
target.options[target.options.length] = new Option(optName, optValue, false, false);
var selected_values=[];
for(var i=0; i < selected.options.length; i++)
selected_values.push(selected.options[i].value);
user_roles.value = selected_values.join(',');
}
function addOption(form) {
var field=form.num_options;
field.value = parseInt(field.value) + 1;
updateForm(form);
}
function removeMapObject(event, object_id) {
event = event || window.event;
g_view.removeObject(object_id);
return preventDefaultEvents(event);
}
addEvent(document, 'mousemove', function(event) {
return resizeMouseMove(event)
&& dragObject(event)
&& addFollowing(event);
});
addEvent(document, 'click', function(event) {
return addClick(event);
});
var popupNN6=document.getElementById && !document.all;
var bDragging=false;
var pwX, pwY, pwTx, pwTy;
var dragObj=null;
function movemouse(e) {
if(bDragging) {
dragObj.style.left = popupNN6 ? (pwTx + e.clientX - pwX) + 'px' : (pwTx + event.clientX - pwX) + 'px';
dragObj.style.top  = popupNN6 ? (pwTy + e.clientY - pwY) + 'px' : (pwTy + event.clientY - pwY) + 'px';
return false;
}
return true;
}
function selectmouse(e) {
bDragging = true;
dragObj = document.getElementById('popupWindow');
pwTx = parseInt(dragObj.style.left+0, 10);
pwTy = parseInt(dragObj.style.top+0, 10);
pwX = popupNN6 ? e.clientX : event.clientX;
pwY = popupNN6 ? e.clientY : event.clientY;
document.body.onmousemove=movemouse;
return false;
}
function popupWindowClose() {
var w=document.getElementById('popupWindow');
if (w)
document.body.removeChild(w);
if (jscolor.picker)
jscolor.picker.owner.hidePicker();
}
function popupWindowPutContent(oContent) {
if(oContent === null || oContent.code === null) {
return false;
}
var oCell=document.getElementById('popupWindowContent');
if(oCell) {
oCell.innerHTML = oContent.code;
executeJS(oCell);
}
}
function popupWindow(title, oContent, sWidth, closable) {
if(oContent === null || oContent.code === null)
return false;
if (typeof closable === 'undefined')
closable = true;
popupWindowClose();
var posX=getScrollLeft() + (pageWidth()/2 - sWidth/2);
var posY=getScrollTop() + 50;
var oContainerDiv=document.createElement('div');
oContainerDiv.setAttribute('id', 'popupWindow');
oContainerDiv.style.left = posX+'px';
oContainerDiv.style.top = posY+'px';
oContainerDiv.style.width = sWidth+'px';
oContainerDiv.url = oContent.url;
if (closable) {
var oClose=document.createElement('div');
oClose.className = 'close';
oClose.onclick = function() {
popupWindowClose();
return false;
};
oClose.appendChild(document.createTextNode('x'));
oContainerDiv.appendChild(oClose);
oClose = null;
}
var oTitle=document.createElement('h1');
oTitle.appendChild(document.createTextNode(title));
oTitle.onmousedown = selectmouse;
oTitle.onmouseup = function() {
bDragging = false;
};
oContainerDiv.appendChild(oTitle);
oTitle = null;
var content=document.createElement('div');
content.setAttribute('id', 'popupWindowContent');
oContainerDiv.appendChild(content);
content = null;
document.body.appendChild(oContainerDiv);
oContainerDiv = null;
popupWindowPutContent(oContent);
return false;
}
var Base=function() {
};
Base.extend = function(_instance, _static) { // subclass
var extend=Base.prototype.extend;
Base._prototyping = true;
var proto=new this();
extend.call(proto, _instance);
delete Base._prototyping;
var constructor=proto.constructor;
proto.constructor = function() {
if (!Base._prototyping) {
if (this._constructing || this.constructor == klass) { // instantiation
this._constructing = true;
constructor.apply(this, arguments);
delete this._constructing;
} else if (arguments[0] !== null) { // casting
return (arguments[0].extend || extend).call(arguments[0], proto);
}
}
return false;
};
var klass=proto.constructor;
klass.ancestor = this;
klass.extend = this.extend;
klass.forEach = this.forEach;
klass.implement = this.implement;
klass.prototype = proto;
klass.toString = this.toString;
klass.valueOf = function(type) {
return (type == "object") ? klass : constructor.valueOf();
};
extend.call(klass, _static);
if (typeof klass.init == "function") {
klass.init();
}
return klass;
};
Base.prototype = {
extend: function(source, value) {
if (arguments.length > 1) { // extending with a name/value pair
var ancestor=this[source];
if (ancestor && (typeof value == "function") && // overriding a method?
(!ancestor.valueOf || ancestor.valueOf() != value.valueOf()) &&
/\bbase\b/.test(value)) {
var method=value.valueOf();
value = function() {
var previous=this.base || Base.prototype.base;
this.base = ancestor;
var returnValue=method.apply(this, arguments);
this.base = previous;
return returnValue;
};
value.valueOf = function(type) {
return (type == "object") ? value : method;
};
value.toString = Base.toString;
}
this[source] = value;
} else if (source) { // extending with an object literal
var extend=Base.prototype.extend;
if (!Base._prototyping && typeof this != "function") {
extend = this.extend || extend;
}
var proto={toSource: null};
var hidden=["constructor", "toString", "valueOf"];
var i=Base._prototyping ? 0 : 1;
var key;
while ((key = hidden[i++])) {
if (source[key] != proto[key]) {
extend.call(this, key, source[key]);
}
}
for (var key in source) {
if (!proto[key]) {
extend.call(this, key, source[key]);
}
}
}
return this;
},
base: function() {
}
};
Base = Base.extend({
constructor: function() {
this.extend(arguments[0]);
}
}, {
ancestor: Object,
version: "1.1",
forEach: function(object, block, context) {
for (var key in object) {
if (this.prototype[key] === undefined) {
block.call(context, object[key], key, object);
}
}
},
implement: function() {
for (var i=0; i < arguments.length; i++) {
if (typeof arguments[i] == "function") {
arguments[i](this.prototype);
} else {
this.prototype.extend(arguments[i]);
}
}
return this;
},
toString: function() {
return String(this.valueOf());
}
});
var frontendMessages={};
function frontendMessagePresent(key) {
return isset(frontendMessages[key]);
}
function frontendMessageRemove(key) {
if(frontendMessagePresent(key)) {
document.body.removeChild(frontendMessages[key]);
delete frontendMessages[key];
}
}
function frontendMessage(oMessage, key) {
var sTitle='';
if (typeof oMessage.title !== 'undefined')
sTitle = oMessage.title;
var closable=true;
if (typeof oMessage.closable !== 'undefined')
closable = oMessage.closable;
if (isset(key) && frontendMessagePresent(key))
return;
popupWindow(sTitle, {'code': '<div class="'+oMessage.type.toLowerCase()+'">'
+oMessage.message+'</div>'}, 500, closable);
if (typeof oMessage.reloadTime !== 'undefined' && oMessage.reloadTime !== null) {
var sUrl=window.location.href;
if(typeof oMessage.reloadUrl !== 'undefined' && oMessage.reloadUrl !== null) {
sUrl = oMessage.reloadUrl;
}
sUrl = sUrl.replace('#', '');
window.setTimeout(function() { window.location.href = sUrl; }, oMessage.reloadTime*1000);
}
}
var _eventlog=null;
var oSeverity={
'debug':    4,
'info':     3,
'warning':  2,
'critical': 1,
'error':    1
};
function eventlogToggle(store) {
var oLog=document.getElementById('eventlog');
var oLogControl=document.getElementById('eventlogControl');
if(store === true)
storeUserOption('eventlog', oLog.style.display == 'none');
if(oLog.style.display != 'none') {
oLog.style.display = 'none';
oLogControl.style.bottom = '0px';
} else {
oLog.style.display = '';
oLog.style.height = oPageProperties.event_log_height+'px';
oLogControl.style.bottom = (parseInt(oPageProperties.event_log_height, 10)+5)+'px';
}
oLog = null;
}
function eventlogInitialize() {
var doc=document;
var oEventlog=doc.createElement('div');
oEventlog.setAttribute("id","eventlog");
oEventlog.style.overflow = 'auto';
oEventlog.style.height = oPageProperties.event_log_height+'px';
var oEventlogControl=doc.createElement('div');
oEventlogControl.setAttribute("id","eventlogControl");
oEventlogControl.style.bottom = (parseInt(oPageProperties.event_log_height, 10)+5)+'px';
oEventlogControl.appendChild(doc.createTextNode('_'));
oEventlogControl.onmouseover = function() {
document.body.style.cursor='pointer';
};
oEventlogControl.onmouseout = function() {
document.body.style.cursor='auto';
};
oEventlogControl.onclick = function() {
eventlogToggle(true);
};
doc.body.appendChild(oEventlog);
doc.body.appendChild(oEventlogControl);
oEventlogControl = null;
if((typeof(oUserProperties.eventlog) !== 'undefined' && oUserProperties.eventlog === false)
|| oPageProperties.event_log_hidden == 1)
eventlogToggle(false);
_eventlog = oEventlog;
oEventlog = null;
doc = null;
}
function eventlog(sComponent, sSeverity, sText) {
if(typeof(oPageProperties) != 'undefined' && oPageProperties !== null && oPageProperties.event_log && oPageProperties.event_log != '0') {
var doc=document;
if(_eventlog === null) {
eventlogInitialize();
eventlog("eventlog", "info", "Eventlog initialized (Level: "+oPageProperties.event_log_level+")");
}
var oEventlog=_eventlog;
if(typeof oSeverity[sSeverity] === 'undefined') {
eventlog('eventlog', 'error', 'Unknown severity used, skipping: '+sSeverity+' '+sComponent+': '+sText)
oEventlog = null;
}
if(oSeverity[sSeverity] <= oSeverity[oPageProperties.event_log_level]) {
if(oEventlog.childNodes && oEventlog.childNodes.length >= oPageProperties.event_log_events * 2) {
oEventlog.removeChild(oEventlog.firstChild);
oEventlog.removeChild(oEventlog.firstChild);
}
var oEntry=doc.createTextNode(getCurrentTime()+" "+sSeverity+" "+sComponent+": "+sText);
oEventlog.appendChild(oEntry);
oEntry = null;
oEventlog.appendChild(doc.createElement('br'));
oEventlog.scrollTop = oEventlog.scrollHeight;
}
oEventlog = null;
doc = null;
}
}
function call_ajax(url, args)
{
args = merge_args({
add_ajax_id      : true,
response_handler : null,
error_handler    : function(status_code, response, handler_data) {
frontendMessage(response, 'serverError');
},
handler_data     : null,
method           : "GET",
post_data        : null,
sync             : false,
decode_json      : true,
}, args);
var AJAX=window.XMLHttpRequest ? new XMLHttpRequest()
: new ActiveXObject("Microsoft.XMLHTTP");
if (!AJAX)
return null;
if (args.add_ajax_id) {
url += url.indexOf('\?') !== -1 ? "&" : "?";
url += "_ajaxid="+iNow;
}
AJAX.open(args.method, url, !args.sync);
if (args.method == "POST") {
if (typeof args.post_data !== 'object')
AJAX.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
}
if (!args.sync) {
AJAX.onreadystatechange = function() {
if (AJAX && AJAX.readyState == 4) {
if (AJAX.status == 200) {
var response=AJAX.responseText;
if (args.decode_json) {
try {
response = JSON.parse(response);
} catch(e) {
args.error_handler(AJAX.status, {
'type'    : 'error',
'title'   : 'Error: Syntax Error',
'message' : "Invalid JSON response<div class=details>\nTime: "
+ iNow + "<br />\nURL: " + url.replace(/</g, '&lt;') + "<br />\n"
+ "Response: <code>" + response + '</code></div>'
}, 0, 'jsonError');
return '';
}
if (isset(response.type) && isset(response.message)) {
args.error_handler(AJAX.status, response, args.handler_data);
return '';
}
frontendMessageRemove('serverError');
}
if (args.response_handler)
args.response_handler(response, args.handler_data);
}
else if (AJAX.status == 401) {
document.location.reload();
}
else if (AJAX.status == 0) {
}
else {
args.error_handler(AJAX.status, null, args.handler_data);
}
}
}
}
AJAX.send(args.post_data);
return AJAX;
}
function getFormParams(formId, skipHelperFields) {
if (window.FormData) {
var data=new FormData();
var formdata=true;
} else {
var formdata=false;
var data='';
}
var add_data=function(key, val) {
if (formdata)
data.append(key, val);
else
data += key + "=" + escapeUrlValues(val) + "&";
};
var oForm=document.getElementById(formId);
if (typeof oForm === 'undefined')
return data;
var aFields=oForm.getElementsByTagName('input');
for (var i=0, len = aFields.length; i < len; i++) {
if (skipHelperFields && aFields[i].name.charAt(0) === '_')
continue;
var oFieldDefault=document.getElementById('_'+aFields[i].name);
if (aFields[i] && oFieldDefault && !document.getElementById('_conf_'+aFields[i].name)) {
if (aFields[i].value === oFieldDefault.value) {
continue;
}
}
oFieldDefault = null;
if (aFields[i].type == "hidden"
|| aFields[i].type == "text"
|| aFields[i].type == "password"
|| aFields[i].type == "submit") {
add_data(aFields[i].name, aFields[i].value);
}
else if (aFields[i].type == "checkbox") {
if (aFields[i].checked) {
add_data(aFields[i].name, aFields[i].value);
}
else {
add_data(aFields[i].name, '');
}
}
else if (aFields[i].type == "radio") {
if (aFields[i].checked) {
add_data(aFields[i].name, aFields[i].value);
}
}
else if (aFields[i].type == "file") {
if (!formdata) {
throw new Error('File upload not supported with your browser. '
+'This form can only be used when using a browser '
+'which suports javascript file uploads (FormData).');
}
if (aFields[i].files.length > 0) {
var file=aFields[i].files[0];
data.append(aFields[i].name, file, file.name);
}
}
}
aFields = oForm.getElementsByTagName('select');
for(var i=0, len = aFields.length; i < len; i++) {
if (skipHelperFields && aFields[i].name.charAt(0) === '_')
continue;
var oFieldDefault=document.getElementById('_'+aFields[i].name);
if(aFields[i] && oFieldDefault) {
if(aFields[i].value === oFieldDefault.value) {
continue;
}
}
oFieldDefault = null;
if(!aFields[i].multiple || aFields[i].multiple !== true) {
if (aFields[i].selectedIndex != -1) {
add_data(aFields[i].name, aFields[i].options[aFields[i].selectedIndex].value);
}
} else {
for (var a=0; a < aFields[i].options.length; a++) {
if (aFields[i].options[a].selected == true) {
add_data(aFields[i].name+'[]', aFields[i].options[a].value);
}
}
}
}
aFields = null;
oForm = null;
return data;
}
function getMidOfAnchor(oObj) {
return [ oObj.x + parseInt(oObj.style.width)  / 2,
oObj.y + parseInt(oObj.style.height) / 2 ];
}
function saveObjectAttr(objId, attr) {
var urlPart='';
for (var key in attr)
urlPart += '&' + key + '=' + escapeUrlValues(attr[key]);
call_ajax(oGeneralProperties.path_server + '?mod=Map&act=modifyObject&map='
+ escapeUrlValues(oPageProperties.map_name) + '&id=' + escapeUrlValues(objId) + urlPart);
}
function saveObjectRemove(objId) {
call_ajax(oGeneralProperties.path_server + '?mod=Map&act=deleteObject&map='
+ escapeUrlValues(oPageProperties.map_name) + '&id=' + escapeUrlValues(objId));
}
var favicon={
change: function(iconURL) {
this.addLink(iconURL, true);
},
addLink: function(iconURL) {
var docHead=document.getElementsByTagName("head")[0];
var link=document.createElement("link");
link.type = "image/x-icon";
link.rel = "shortcut icon";
link.href = iconURL;
this.removeLinkIfExists();
docHead.appendChild(link);
link = null;
docHead = null;
},
removeLinkIfExists: function() {
var docHead=document.getElementsByTagName("head")[0];
var links=docHead.getElementsByTagName("link");
if(!docHead || !links)
return false;
for (var i=0, len = links.length; i<len; i++) {
if (links[i] && links[i].type == "image/x-icon" && links[i].rel == "shortcut icon") {
docHead.removeChild(links[i]);
}
}
links = null;
docHead = null;
return true;
}
};
var Element=Base.extend({
obj     : null,
dom_obj : null,
constructor: function(obj) {
this.obj = obj;
},
update: function() {},
updateAttrs: function(only_state, is_locked) {
if (!only_state) {
this.erase();
this.render();
if (!is_locked)
this.unlock();
this.draw();
}
},
render: function() {},
place: function() {},
draw: function() {
if (this.dom_obj)
this.obj.dom_obj.appendChild(this.dom_obj);
},
erase: function() {
if (this.dom_obj && this.dom_obj.parentNode)
this.obj.dom_obj.removeChild(this.dom_obj);
},
lock: function() {},
unlock: function() {},
addTo: function(obj) {
obj.addElement(this);
return this;
},
removeFrom: function(obj) {
obj.removeElement(this);
return this;
},
toggleLink: function(enable) {
if (enable) {
if (this.obj.trigger_obj.parentNode.tagName == 'A') {
this.obj.trigger_obj.parentNode.onclick = null;
}
} else if (!enable) {
if (this.obj.trigger_obj.parentNode.tagName == 'A') {
this.obj.trigger_obj.parentNode.onclick = function(event) {
var event=!event ? window.event : event;
if(event.stopPropagation)
event.stopPropagation();
event.cancelBubble = true;
return false;
};
}
}
}
});
var g_context_templates={};
var g_context_open=null;
function contextHide() {
if (g_context_open !== null)
g_context_open.hide();
}
function context_handle_global_mousedown(event) {
event = event ? event : window.event; // IE FIX
if (usesSource('worldmap'))
event = event.originalEvent;
var target=getTargetRaw(event);
while (target && !has_class(target, 'context'))
target = target.parentNode;
if (target === null) {
contextHide();
}
else {
var object_id=target.id.split('-')[0];
if (object_id == g_context_open.obj.conf.object_id)
return preventDefaultEvents(event);
}
}
var ElementContext=Element.extend({
template_html : null,
spacing       : 5,    // px from screen border
coords        : null, // list of x, y coordinates of the hover menu top left corner
update: function() {
this.getTemplate();
},
render: function() {
this.getTemplate();
if (this.template_html === null || this.template_html === true)
return false; // template not available yet, skip rendering
this.renderMenu();
},
draw: function() {
if (this.dom_obj === null)
this.render();
this.base();
addEvent(this.obj.trigger_obj, 'contextmenu', function(element_obj) {
return function(event) {
if (element_obj.dom_obj === null) {
element_obj.draw();
}
element_obj.coords = [event.clientX, event.clientY];
element_obj.show();
return preventDefaultEvents(event);
};
}(this));
},
erase: function() {
removeEvent(this.obj.trigger_obj, 'mousedown');
removeEvent(this.obj.trigger_obj, 'contextmenu');
this.base();
},
lock: function() {
this.erase();
this.render();
this.draw();
},
unlock: function() {
this.erase();
this.render();
this.draw();
},
getTemplate: function() {
var name=this.obj.conf.context_template;
if (!isset(g_context_templates[name])) {
this.requestTemplate();
}
else if (g_context_templates[name] !== true) {
this.template_html = g_context_templates[name];
this.replaceStaticMacros();
}
},
handleTemplate: function (templates) {
var name=templates[0]['name'];
var code=templates[0]['code'];
g_context_templates[name] = code;
this.getTemplate(); // assign template to the object
if (isset(templates[0]['css_file'])) {
var oLink=document.createElement('link');
oLink.href = templates[0]['css_file'];
oLink.rel = 'stylesheet';
oLink.type = 'text/css';
document.getElementsByTagName("head")[0].appendChild(oLink);
}
},
requestTemplate: function () {
call_ajax(oGeneralProperties.path_server+'?mod=General&act=getContextTemplate'
+'&name[]='+escapeUrlValues(this.obj.conf.context_template), {
response_handler: this.handleTemplate.bind(this)
});
g_context_templates[this.obj.conf.context_template] = true; // mark as already requested
},
show: function() {
hoverHide();
var scrollTop=document.body.scrollTop ? document.body.scrollTop :
document.documentElement.scrollTop;
var scrollLeft=document.body.scrollLeft ? document.body.scrollLeft :
document.documentElement.scrollLeft;
this.dom_obj.style.display = 'none';
this.dom_obj.style.left = this.coords[0] + this.spacing + scrollLeft - getSidebarWidth() + 'px';
this.dom_obj.style.top = this.coords[1] + this.spacing + scrollTop - getHeaderHeight() + 'px';
this.dom_obj.style.display = '';
var contextLeft=parseInt(this.dom_obj.style.left.replace('px', ''));
if(contextLeft+this.dom_obj.clientWidth > pageWidth()) {
this.dom_obj.style.left = contextLeft - this.dom_obj.clientWidth + 'px';
}
var contextTop=parseInt(this.dom_obj.style.top.replace('px', ''));
if(contextTop+this.dom_obj.clientHeight > pageHeight()) {
if(contextTop - this.dom_obj.clientHeight >= 0) {
this.dom_obj.style.top = contextTop - this.dom_obj.clientHeight + 'px';
}
}
g_context_open = this;
},
hide: function() {
if (this.dom_obj) {
this.dom_obj.style.display = 'none';
}
g_context_open = null;
},
renderMenu: function () {
var contextMenu=document.createElement('div');
this.dom_obj = contextMenu;
contextMenu.setAttribute('id', this.obj.conf.object_id+'-context');
contextMenu.className = 'context';
contextMenu.style.display = 'none';
contextMenu.innerHTML = this.template_html;
},
replaceStaticMacros: function() {
var oSectionMacros={};
if(!this.template_html || this.template_html === '') {
return false;
}
var oMacros={
'obj_id':      this.obj.conf.object_id,
'type':        this.obj.conf.type,
'name':        this.obj.conf.name,
'alias':       this.obj.conf.alias,
'address':     this.obj.conf.address,
'html_cgi':    this.obj.conf.htmlcgi,
'backend_id':  this.obj.conf.backend_id,
'custom_1':    this.obj.conf.custom_1,
'custom_2':    this.obj.conf.custom_2,
'custom_3':    this.obj.conf.custom_3
};
if (g_view.type === 'map')
oMacros.map_name = g_view.id;
if(this.obj.conf.type === 'service') {
oMacros.service_description = escapeUrlValues(this.obj.conf.service_description);
oMacros.pnp_hostname = this.obj.conf.name.replace(/\s/g,'%20');
oMacros.pnp_service_description = this.obj.conf.service_description.replace(/\s/g,'%20');
} else
oSectionMacros.service = '<!--\\sBEGIN\\sservice\\s-->.+?<!--\\sEND\\sservice\\s-->';
if(this.obj.conf.type === 'host')
oMacros.pnp_hostname = this.obj.conf.name.replace(/\s/g,'%20');
else
oSectionMacros.host = '<!--\\sBEGIN\\shost\\s-->.+?<!--\\sEND\\shost\\s-->';
if(this.obj.conf.type !== 'host' && this.obj.conf.type !== 'shape')
oSectionMacros.host_or_shape = '<!--\\sBEGIN\\shost_or_shape\\s-->.+?<!--\\sEND\\shost_or_shape\\s-->';
if(this.obj.conf.type === 'line' || this.obj.conf.type == 'shape'
|| this.obj.conf.type == 'textbox' || this.obj.conf.type === 'container')
oSectionMacros.stateful = '<!--\\sBEGIN\\sstateful\\s-->.+?<!--\\sEND\\sstateful\\s-->';
if(this.obj.bIsLocked)
oSectionMacros.unlocked = '<!--\\sBEGIN\\sunlocked\\s-->.+?<!--\\sEND\\sunlocked\\s-->';
else
oSectionMacros.locked = '<!--\\sBEGIN\\slocked\\s-->.+?<!--\\sEND\\slocked\\s-->';
if(!oViewProperties || !oViewProperties.permitted_edit)
oSectionMacros.permitted_edit = '<!--\\sBEGIN\\spermitted_edit\\s-->.+?<!--\\sEND\\spermitted_edit\\s-->';
if(!oViewProperties || !oViewProperties.permitted_perform)
oSectionMacros.permitted_perform = '<!--\\sBEGIN\\spermitted_perform\\s-->.+?<!--\\sEND\\spermitted_perform\\s-->';
if(usesSource('automap')) {
oSectionMacros.not_automap = '<!--\\sBEGIN\\snot_automap\\s-->.+?<!--\\sEND\\snot_automap\\s-->';
if(this.obj.conf.name === getUrlParam('root'))
oSectionMacros.automap_not_root = '<!--\\sBEGIN\\sautomap_not_root\\s-->.+?<!--\\sEND\\sautomap_not_root\\s-->';
} else {
oSectionMacros.automap_not_root = '<!--\\sBEGIN\\sautomap_not_root\\s-->.+?<!--\\sEND\\sautomap_not_root\\s-->';
oSectionMacros.automap = '<!--\\sBEGIN\\sautomap\\s-->.+?<!--\\sEND\\sautomap\\s-->';
}
if(this.obj.conf.view_type !== 'line')
oSectionMacros.line = '<!--\\sBEGIN\\sline\\s-->.+?<!--\\sEND\\sline\\s-->';
if(this.obj.conf.view_type !== 'line'
|| (this.obj.conf.line_type == 11 || this.obj.conf.line_type == 12))
oSectionMacros.line_type = '<!--\\sBEGIN\\sline_two_parts\\s-->.+?<!--\\sEND\\sline_two_parts\\s-->';
if(this.obj.conf.type !== 'hostgroup')
oSectionMacros.hostgroup = '<!--\\sBEGIN\\shostgroup\\s-->.+?<!--\\sEND\\shostgroup\\s-->';
if(this.obj.conf.type !== 'servicegroup' && !(this.obj.conf.type === 'dyngroup' && this.obj.conf.object_types == 'service'))
oSectionMacros.servicegroup = '<!--\\sBEGIN\\sservicegroup\\s-->.+?<!--\\sEND\\sservicegroup\\s-->';
if(this.obj.conf.type !== 'map')
oSectionMacros.map = '<!--\\sBEGIN\\smap\\s-->.+?<!--\\sEND\\smap\\s-->';
for (var key in oGeneralProperties.actions) {
if(key == "indexOf")
continue; // skip indexOf prototype (seems to be looped in IE)
var action=oGeneralProperties.actions[key];
var hide=false;
hide = action.obj_type.indexOf(this.obj.conf.type) == -1;
if(!hide && isset(action.client_os) && action.client_os.length > 0) {
var os=navigator.platform.toLowerCase();
if (os.indexOf('win') !== -1)
os = 'win';
else if (os.indexOf('linux') !== -1)
os = 'lnx';
else if (os.indexOf('mac') !== -1)
os = 'mac';
hide = action.client_os.indexOf(os) == -1;
}
if(!hide && isset(action.condition) && action.condition !== '') {
var cond=action.condition;
var op='';
if (cond.indexOf('~') != -1) {
op = '~';
} else if (cond.indexOf('=') != -1) {
op = '=';
}
var parts=cond.split(op);
var attr=parts[0];
var val=parts[1];
var to_be_checked;
if (isset(this.obj.conf.custom_variables) && isset(this.obj.conf.custom_variables[attr])) {
to_be_checked = this.obj.conf.custom_variables[attr];
} else if(isset(this.obj.conf[attr])) {
to_be_checked = this.obj.conf[attr];
}
if (to_be_checked) {
if (op == '=' && to_be_checked != val) {
hide = true;
} else if (op == '~' && to_be_checked.indexOf(val) == -1) {
hide = true;
}
} else {
hide = true;
}
}
if(!hide) {
oSectionMacros['action_'+key] = '<!--\\s(BEGIN|END)\\saction_'+key+'\\s-->';
}
cond = null;
action = null;
}
oSectionMacros['actions'] = '<!--\\sBEGIN\\saction_.+?\\s-->.+?<!--\\sEND\\saction_.+?\\s-->';
for (var key in oSectionMacros) {
var regex=getRegEx('section-'+key, oSectionMacros[key], 'gm');
this.template_html = this.template_html.replace(regex, '');
regex = null;
}
oSectionMacros = null;
this.template_html = this.template_html.replace(/\[(\w*)\]/g,
function(){ return oMacros[ arguments[1] ] || '';});
oMacros = null;
}
});
var g_hover_templates={};
var g_hover_template_childs={};
var g_hover_urls={};
var g_hover_open=null;
function hoverHide() {
if (g_hover_open !== null)
g_hover_open.hide();
}
var ElementHover=Element.extend({
hover_url      : null,  // configured url with eventual replaced macros
template_html  : null,  // hover HTML code with replaced config related macros
coords         : null,  // list of x, y coordinates of the hover menu top left corner
show_timer     : null,  // JS timer when hover delay is used
spacing        : 5,     // px from screen border
min_width      : 400,   // px minimum width
enabled        : false, // when true the event handlers are enabled
update: function() {
this.hover_url = this.obj.conf.hover_url;
if (this.hover_url && this.hover_url !== '') {
this.hover_url = this.hover_url.replace(getRegEx(name,
'\\['+name+'\\]', 'g'), this.obj.conf.name);
if (this.obj.conf.type == 'service')
this.hover_url = this.hover_url.replace(getRegEx('service_description',
'\\[service_description\\]', 'g'), this.obj.conf.service_description);
}
this.getTemplate();
},
updateAttrs: function(only_state) {
this.render();
},
render: function() {
this.getTemplate();
if (this.obj.bIsLocked)
this.enable();
if (this.template_html === null || this.template_html === true)
return false; // template not available yet, skip rendering
if (this.dom_obj)
this._render();
},
draw: function() {
if (this.obj.bIsLocked) {
if (!this.dom_obj)
this._render();
this.base();
}
},
erase: function() {
this.disable();
this.base();
},
lock: function() {
this.enable();
},
unlock: function() {
this.disable();
},
_render: function() {
this.getTemplate();
if (this.template_html === null || this.template_html === true) {
return false; // template not available yet, skip rendering
}
this.renderMenu();
},
getTemplate: function() {
if (this.hover_url && this.hover_url !== '') {
if (!isset(g_hover_urls[this.hover_url])) {
this.requestUrl();
}
else {
this.template_html = g_hover_urls[this.hover_url];
}
}
else {
var name=this.obj.conf.hover_template;
if (!isset(g_hover_templates[name])) {
this.requestTemplate();
}
else if (g_hover_templates[name] !== true) {
this.template_html = g_hover_templates[name];
this.replaceStaticMacros();
}
}
},
handleUrl: function (urls) {
g_hover_urls[urls[0]['url']] = urls[0]['code'];
this.getTemplate(); // assign template to the object
},
requestUrl: function () {
call_ajax(oGeneralProperties.path_server+'?mod=General&act=getHoverUrl'
+'&url[]='+escapeUrlValues(this.hover_url), {
response_handler: this.handleUrl.bind(this)
});
g_hover_urls[this.hover_url] = true; // mark as already requested
},
getChildCode: function (template_html) {
var regex=getRegEx('loopChild', "<!--\\sBEGIN\\sloop_child\\s-->(.+?)<!--\\sEND\\sloop_child\\s-->");
var results=regex.exec(template_html);
if (results !== null)
return results[1];
else
return '';
},
handleTemplate: function (templates) {
var name=templates[0]['name'];
var code=templates[0]['code'];
g_hover_templates[name] = code;
g_hover_template_childs[name] = this.getChildCode(code);
this.getTemplate(); // assign template to the object
if (isset(templates[0]['css_file'])) {
var oLink=document.createElement('link');
oLink.href = templates[0]['css_file'];
oLink.rel = 'stylesheet';
oLink.type = 'text/css';
document.getElementsByTagName("head")[0].appendChild(oLink);
}
},
requestTemplate: function () {
call_ajax(oGeneralProperties.path_server+'?mod=General&act=getHoverTemplate'
+'&name[]='+escapeUrlValues(this.obj.conf.hover_template), {
response_handler: this.handleTemplate.bind(this)
});
g_hover_templates[this.obj.conf.hover_template] = true; // mark as already requested
},
enable: function() {
if (!this.enabled) {
this._handleMouseMove = this.handleMouseMove.bind(this);
this._handleMouseOut  = this.handleMouseOut.bind(this);
addEvent(this.obj.trigger_obj, 'mousemove', this._handleMouseMove);
addEvent(this.obj.trigger_obj, 'mouseout', this._handleMouseOut);
addEvent(this.obj.trigger_obj, 'mousedown', this._handleMouseOut);
this.enabled = true;
}
},
disable: function() {
if (this.enabled) {
removeEvent(this.obj.trigger_obj, 'mousemove', this._handleMouseMove);
removeEvent(this.obj.trigger_obj, 'mouseout', this._handleMouseOut);
removeEvent(this.obj.trigger_obj, 'mousedown', this._handleMouseOut);
this.enabled = false;
}
},
handleMouseOut: function(event) {
this.hide();
},
handleMouseMove: function(event) {
event = event ? event : window.event; // IE FIX
if (this.dom_obj === null)
this.draw();
var hover_delay=parseInt(this.obj.conf.hover_delay);
if (!dragging() && g_context_open === null && this.show_timer === null) {
this.coords = [event.clientX, event.clientY];
if (hover_delay && !this.isVisible()) {
this.show_timer = setTimeout(function(obj) {
return function() {
obj.show();
};
}(this), hover_delay*1000);
}
else {
this.show();
}
}
},
isVisible: function() {
return this.dom_obj.style.display !== 'none';
},
show: function() {
if (this.dom_obj)
this.showAndPositionMenu();
},
hide: function() {
if (this.show_timer !== null) {
clearTimeout(this.show_timer);
this.show_timer = null;
}
if (this.dom_obj)
this.dom_obj.style.display = 'none';
this.coords = null;
g_hover_open = null;
},
showAndPositionMenu: function() {
var scrollTop=document.body.scrollTop ? document.body.scrollTop :
document.documentElement.scrollTop;
var scrollLeft=document.body.scrollLeft ? document.body.scrollLeft :
document.documentElement.scrollLeft;
var x=this.coords[0],
y = this.coords[1];
this.dom_obj.style.display = 'none';
this.dom_obj.style.left = (x + scrollLeft + this.spacing - getSidebarWidth()) + 'px';
this.dom_obj.style.top = (y + scrollTop + this.spacing - getHeaderHeight()) + 'px';
if(isIE) {
this.dom_obj.style.width = '0px';
} else {
this.dom_obj.style.width = 'auto';
}
this.dom_obj.style.display = '';
g_hover_open = this;
if(this.dom_obj.clientWidth - this.spacing > this.min_width)
this.dom_obj.style.width = this.dom_obj.clientWidth - this.spacing + 'px';
else
this.dom_obj.style.width = this.min_width + 'px';
var hoverLeft=parseInt(this.dom_obj.style.left.replace('px', ''));
var screenWidth=pageWidth();
var hoverPosAndSizeOk=true;
if (!this.isOnScreen()) {
hoverPosAndSizeOk = false;
if (this.tryResize())
hoverPosAndSizeOk = true;
}
if (!hoverPosAndSizeOk) {
if (this.dom_obj.clientWidth < this.min_width) {
this.dom_obj.style.left = (x - this.min_width - this.spacing + scrollLeft) + 'px';
} else {
this.dom_obj.style.left = (x - this.dom_obj.clientWidth - this.spacing + scrollLeft) + 'px';
}
if (this.isOnScreen()) {
hoverPosAndSizeOk = true;
} else {
if (this.tryResize(true)) {
hoverPosAndSizeOk = true;
}
}
}
if (!this.isOnScreen()) {
this.dom_obj.style.left = this.spacing + scrollLeft + 'px';
this.dom_obj.style.width = pageWidth() - (2*this.spacing) + 'px';
}
var hoverTop=parseInt(this.dom_obj.style.top.replace('px', ''));
if(hoverTop + this.dom_obj.clientHeight > pageHeight() && hoverTop - this.dom_obj.clientHeight >= 0)
this.dom_obj.style.top = hoverTop - this.dom_obj.clientHeight - this.spacing - 5 + 'px';
hoverTop = null;
},
isOnScreen: function() {
var hoverLeft=parseInt(this.dom_obj.style.left.replace('px', ''));
var scrollLeft=document.body.scrollLeft ? document.body.scrollLeft :
document.documentElement.scrollLeft;
if (hoverLeft < scrollLeft)
return false;
var hoverRight=hoverLeft + this.dom_obj.clientWidth - scrollLeft;
var viewRight=pageWidth();
if (hoverRight > viewRight)
return false;
if (hoverLeft - this.spacing < 0)
return false;
return true;
},
tryResize: function(rightSide) {
if (!isset(rightSide))
var reposition=false;
var hoverLeft=parseInt(this.dom_obj.style.left.replace('px', ''));
if (rightSide)
var overhead=hoverLeft + this.dom_obj.clientWidth + this.spacing - pageWidth();
else
var overhead=hoverLeft;
var widthAfterResize=this.dom_obj.clientWidth - overhead;
if (widthAfterResize > this.min_width) {
this.dom_obj.style.width = widthAfterResize + 'px';
if (rightSide) {
if(overhead < 0)
overhead *= -1
this.dom_obj.style.left = (hoverLeft + overhead) + 'px';
}
return true;
} else {
return false;
}
},
renderMenu: function () {
var template_html=this.template_html;
if (!this.obj.conf.hover_url || this.obj.conf.hover_url === '') {
if (isset(this.obj.conf.hover_template))
template_html = this.replaceDynamicMacros(template_html);
}
var hoverMenu=document.getElementById(this.obj.conf.object_id+'-hover');
if(!hoverMenu) {
var hoverMenu=document.createElement('div');
this.dom_obj = hoverMenu;
hoverMenu.setAttribute('id', this.obj.conf.object_id+'-hover');
hoverMenu.className = 'hover';
hoverMenu.style.display = 'none';
}
hoverMenu.innerHTML = template_html;
if (this.coords !== null)
this.show();
},
replaceChildMacros: function (template_html) {
var childs_html='';
var regex='';
var row_tmpl=g_hover_template_childs[this.obj.conf.hover_template];
var stateful_members=this.obj.getStatefulMembers();
if(typeof(row_tmpl) != 'undefined' && row_tmpl != '' && stateful_members.length > 0) {
for(var i=0, len1 = this.obj.conf.hover_childs_limit, len2 = stateful_members.length;
(len1 == -1 || (len1 >= 0 && i <= len1)) && i < len2; i++) {
if(len1 == -1 || (len1 >= 0 && i < len1)) {
stateful_members[i].parent_type = this.obj.conf.type;
stateful_members[i].parent_name = this.obj.conf.name;
childs_html += this.replaceMacrosOfChild(stateful_members[i], row_tmpl);
} else {
var member={
'conf': {
'type': 'host',
'name': '',
'summary_state': '',
'summary_output': (this.obj.conf.num_members - this.obj.conf.hover_childs_limit) + ' ' + _('more items...'),
'<!--\\sBEGIN\\sservicegroup_child\\s-->.+?<!--\\sEND\\sservicegroup_child\\s-->': ''
}
};
childs_html += this.replaceMacrosOfChild(member, row_tmpl);
}
}
}
if(childs_html != '')
regex = getRegEx('loopChild', "<!--\\sBEGIN\\sloop_child\\s-->(.+?)<!--\\sEND\\sloop_child\\s-->");
else
regex = getRegEx('loopChildEmpty', '<!--\\sBEGIN\\schilds\\s-->.+?<!--\\sEND\\schilds\\s-->');
template_html = template_html.replace(regex, childs_html);
return template_html;
},
replaceMacrosOfChild: function (member_obj, template_html) {
var oMacros={
'obj_summary_state'  : member_obj.conf.summary_state,
'obj_summary_output' : member_obj.conf.summary_output,
'obj_display_name'   : member_obj.conf.display_name
}
if (member_obj.conf.summary_problem_has_been_acknowledged && member_obj.conf.summary_problem_has_been_acknowledged == 1)
oMacros.obj_summary_acknowledged = '(Acknowledged)';
if (member_obj.conf.summary_in_downtime && member_obj.conf.summary_in_downtime == 1)
oMacros.obj_summary_in_downtime = '(Downtime)';
if (member_obj.conf.summary_stale)
oMacros.obj_summary_stale = '(Stale)';
if (member_obj.conf.type === 'service')
oMacros.obj_name = member_obj.conf.service_description;
else
oMacros.obj_name = member_obj.conf.name;
if ((member_obj.parent_type === 'servicegroup' || member_obj.parent_type === 'dyngroup')
&& member_obj.conf.type === 'service')
oMacros.obj_name1 = member_obj.conf.name;
else {
var regex=getRegEx('section-sgchild', '<!--\\sBEGIN\\sservicegroup_child\\s-->.+?<!--\\sEND\\sservicegroup_child\\s-->', 'gm');
if (template_html.search(regex) !== -1)
template_html = template_html.replace(regex, '');
}
template_html = template_html.replace(/\[(\w*)\]/g, function() {
return oMacros[ arguments[1] ] || "";
});
return template_html;
},
replaceDynamicMacros: function (template_html) {
var oMacros={};
if (g_view.type === 'map')
oMacros.map_name = oPageProperties.map_name;
oMacros.last_status_refresh = date(oGeneralProperties.date_format, this.obj.lastUpdate);
oMacros.obj_state = this.obj.conf.state;
oMacros.obj_summary_state = this.obj.conf.summary_state;
if (this.obj.conf.summary_problem_has_been_acknowledged && this.obj.conf.summary_problem_has_been_acknowledged === 1)
oMacros.obj_summary_acknowledged = '(Acknowledged)';
if (this.obj.conf.problem_has_been_acknowledged && this.obj.conf.problem_has_been_acknowledged === 1)
oMacros.obj_acknowledged = '(Acknowledged)';
if (this.obj.conf.summary_in_downtime && this.obj.conf.summary_in_downtime === 1)
oMacros.obj_summary_in_downtime = '(Downtime)';
if (this.obj.conf.in_downtime && this.obj.conf.in_downtime === 1)
oMacros.obj_in_downtime = '(Downtime)';
if (this.obj.conf.summary_stale)
oMacros.obj_summary_stale = '(Stale)';
if (this.obj.conf.stale)
oMacros.obj_stale = '(Stale)';
oMacros.obj_output = this.obj.conf.output;
oMacros.obj_summary_output = this.obj.conf.summary_output;
if (this.obj.conf.type === 'host' || this.obj.conf.type === 'service') {
oMacros.obj_last_check = this.obj.conf.last_check;
oMacros.obj_next_check = this.obj.conf.next_check;
oMacros.obj_state_type = this.obj.conf.state_type;
oMacros.obj_current_check_attempt = this.obj.conf.current_check_attempt;
oMacros.obj_max_check_attempts = this.obj.conf.max_check_attempts;
oMacros.obj_last_state_change = this.obj.conf.last_state_change;
oMacros.obj_last_hard_state_change = this.obj.conf.last_hard_state_change;
oMacros.obj_state_duration = this.obj.conf.state_duration;
oMacros.obj_perfdata = this.obj.conf.perfdata;
}
if (this.obj.firstUpdate !== null) {
var regex=getRegEx('img_timestamp', '_t='+this.obj.firstUpdate, 'g');
if(template_html.search(regex) !== -1)
template_html = template_html.replace(regex, '_t='+this.obj.lastUpdate);
}
if (this.obj.conf.hover_childs_show && this.obj.conf.hover_childs_show == '1')
template_html = this.replaceChildMacros(template_html);
template_html = template_html.replace(/\[(\w*)\]/g, function() {
return oMacros[ arguments[1] ] || "";
});
return template_html;
},
replaceStaticMacros: function() {
var oMacros={};
var oSectionMacros={};
if(this.obj.conf.type && this.obj.conf.type != '')
oMacros.obj_type = this.obj.conf.type;
oMacros.lang_obj_type = _(this.obj.conf.type);
if (this.obj.conf.type == 'host') {
oMacros.lang_name        = _('hostname');
oMacros.lang_child_name  = _('servicename');
} else if (this.obj.conf.type == 'service') {
oMacros.lang_name        = _('servicename');
} else if (this.obj.conf.type == 'hostgroup') {
oMacros.lang_name        = _('hostgroupname');
oMacros.lang_child_name  = _('hostname');
} else if (this.obj.conf.type == 'servicegroup') {
oMacros.lang_name        = _('servicegroupname');
oMacros.lang_child_name  = _('servicename');
oMacros.lang_child_name1 = _('hostname');
} else if (this.obj.conf.type == 'dyngroup') {
oMacros.lang_name        = _('Dynamic Group Name');
oMacros.lang_child_name  = _('Object Name');
if (this.obj.conf.object_types == 'service')
oMacros.lang_child_name1 = _('hostname');
} else if (this.obj.conf.type == 'aggr') {
oMacros.lang_name        = _('Aggregation Name');
oMacros.lang_child_name  = _('Name');
oMacros.lang_child_name1 = _('Name');
} else if (this.obj.conf.type == 'map') {
oMacros.lang_name        = _('mapname');
oMacros.lang_child_name  = _('objectname');
}
oMacros.obj_name = this.obj.conf.name;
if(this.obj.conf.alias && this.obj.conf.alias !== '') {
oMacros.obj_alias        = this.obj.conf.alias;
oMacros.obj_alias_braces = ' (' +this.obj.conf.alias + ')';
} else {
oMacros.obj_alias        = '';
oMacros.obj_alias_braces = '';
}
if(this.obj.conf.display_name && this.obj.conf.display_name !== '')
oMacros.obj_display_name = this.obj.conf.display_name;
else
oMacros.obj_display_name = '';
if(this.obj.conf.notes && this.obj.conf.notes !== '')
oMacros.obj_notes = this.obj.conf.notes;
else
oMacros.obj_notes = '';
if(this.obj.conf.type !== 'map') {
oMacros.obj_backendid = this.obj.conf.backend_id;
oMacros.obj_backend_instancename = this.obj.conf.backend_instancename;
oMacros.html_cgi = this.obj.conf.htmlcgi;
oMacros.custom_1 = this.obj.conf.custom_1;
oMacros.custom_2 = this.obj.conf.custom_2;
oMacros.custom_3 = this.obj.conf.custom_3;
} else {
oMacros.obj_backendid = '';
oMacros.obj_backend_instancename = '';
oMacros.html_cgi = '';
oMacros.custom_1 = '';
oMacros.custom_2 = '';
oMacros.custom_3 = '';
}
if(this.obj.conf.type === 'host' || this.obj.conf.type === 'service') {
oMacros.obj_address = this.obj.conf.address;
oMacros.obj_tags    = this.obj.conf.tags.join(', ');
for (var group_id in this.obj.conf.taggroups) {
var group=this.obj.conf.taggroups[group_id];
oMacros['obj_taggroup_' + group_id + '_title'] = group.title;
oMacros['obj_taggroup_' + group_id + '_topic'] = group.topic;
if (group.value) {
oMacros['obj_taggroup_' + group_id + '_value']       = group.value[0];
oMacros['obj_taggroup_' + group_id + '_value_title'] = group.value[1];
} else {
oMacros['obj_taggroup_' + group_id + '_value']       = '';
oMacros['obj_taggroup_' + group_id + '_value_title'] = '';
}
}
} else {
oMacros.obj_address = '';
oMacros.obj_tags    = '';
}
if (oMacros.obj_tags == '') {
oSectionMacros.has_tags = '<!--\\sBEGIN\\shas_tags\\s-->.+?<!--\\sEND\\shas_tags\\s-->';
}
if(this.obj.conf.type === 'service') {
oMacros.service_description = this.obj.conf.service_description;
oMacros.pnp_hostname = this.obj.conf.name.replace(/\s/g,'%20');
oMacros.pnp_service_description = this.obj.conf.service_description.replace(/\s/g,'%20');
} else
oSectionMacros.service = '<!--\\sBEGIN\\sservice\\s-->.+?<!--\\sEND\\sservice\\s-->';
if(this.obj.conf.type === 'host')
oMacros.pnp_hostname = this.obj.conf.name.replace(' ','%20');
else
oSectionMacros.host = '<!--\\sBEGIN\\shost\\s-->.+?<!--\\sEND\\shost\\s-->';
if(this.obj.conf.type !== 'servicegroup' && !(this.obj.conf.type === 'dyngroup' && this.obj.conf.object_types == 'service')) {
oSectionMacros.servicegroup = '<!--\\sBEGIN\\sservicegroup\\s-->.+?<!--\\sEND\\sservicegroup\\s-->';
}
if(this.obj.conf.type !== 'hostgroup')
oSectionMacros.hostgroup = '<!--\\sBEGIN\\shostgroup\\s-->.+?<!--\\sEND\\shostgroup\\s-->';
if(this.obj.conf.type !== 'map')
oSectionMacros.map = '<!--\\sBEGIN\\smap\\s-->.+?<!--\\sEND\\smap\\s-->';
if(this.obj.conf.hover_childs_show && this.obj.conf.hover_childs_show != '1')
oSectionMacros.childs = '<!--\\sBEGIN\\schilds\\s-->.+?<!--\\sEND\\schilds\\s-->';
for (var key in oSectionMacros) {
var regex=getRegEx('section-'+key, oSectionMacros[key], 'gm');
if (this.template_html.search(regex) !== -1)
this.template_html = this.template_html.replace(regex, '');
regex = null;
}
this.template_html = this.template_html.replace(/\[(\w*)\]/g, function() {
return oMacros[ arguments[1] ] || '['+arguments[1]+']';
});
var regex=getRegEx('loopChild', "<!--\\sBEGIN\\sloop_child\\s-->(.+?)<!--\\sEND\\sloop_child\\s-->");
if(this.template_html.search(regex) !== -1)
this.template_html = this.template_html.replace(regex, '<!-- BEGIN loop_child -->'
+ g_hover_template_childs[this.obj.hover_template]
+ '<!-- END loop_child -->');
var regex=getRegEx('img', "<img.*src=['\"]?([^>'\"]*)['\"]?");
var results=regex.exec(this.template_html);
if(results !== null) {
for(var i=0, len = results.length; i < len; i=i+2) {
var sTmp=results[i].replace(results[i+1], results[i+1]+"&_t="+this.obj.firstUpdate);
this.template_html = this.template_html.replace(results[i], sTmp);
}
}
}
});
var ElementIcon=Element.extend({
render: function() {
this.renderIcon();
this.place();
},
place: function () {
this.dom_obj.style.top  = this.obj.parseCoord(this.obj.conf.y, 'y') + 'px';
this.dom_obj.style.left = this.obj.parseCoord(this.obj.conf.x, 'x') + 'px';
},
unlock: function () {
this.toggleLink(false);
makeDragable(this.dom_obj, this.obj, this.obj.saveObject, this.obj.moveObject);
},
lock: function () {
this.toggleLink(true);
makeUndragable(this.dom_obj);
},
renderIcon: function () {
var alt='';
if(this.obj.conf.type == 'service')
alt = this.obj.conf.name+'-'+this.obj.conf.service_description;
else
alt = this.obj.conf.name;
var oIcon=document.createElement('img');
oIcon.setAttribute('id', this.obj.conf.object_id+'-icon');
oIcon.className = 'icon';
this.obj.trigger_obj = oIcon;
if (this.obj.conf.icon_size) {
var size=this.obj.conf.icon_size;
if (size.length == 1) {
var w=parseInt(size),
h = parseInt(size);
} else {
var w=parseInt(size[0]),
h = parseInt(size[1]);
}
oIcon.style.width = w + 'px';
oIcon.style.height = h + 'px';
}
addEvent(oIcon, 'load', function(obj) {
return function() {
obj.place();
obj = null;
};
}(this.obj));
addZoomHandler(oIcon);
oIcon.src = oGeneralProperties.path_iconsets + this.obj.conf.icon;
oIcon.alt = this.obj.conf.type + '-' + alt;
var oIconDiv=document.createElement('div');
this.dom_obj = oIconDiv;
oIconDiv.setAttribute('id', this.obj.conf.object_id+'-icondiv');
oIconDiv.className = 'icondiv';
oIconDiv.style.zIndex = this.obj.conf.z;
if (this.obj.conf.url && this.obj.conf.url !== '' && this.obj.conf.url !== '#') {
var oIconLink=document.createElement('a');
oIconLink.href = this.obj.conf.url;
oIconLink.target = this.obj.conf.url_target;
oIconLink.appendChild(oIcon);
oIconDiv.appendChild(oIconLink);
} else {
oIconDiv.appendChild(oIcon);
}
}
});
var ElementLineControls=Element.extend({
render: function() {
if (this.dom_obj)
this._render();
},
draw: function() {
if (!this.obj.bIsLocked)
this.base();
},
unlock: function() {
if (!this.dom_obj)
this._render();
this._draw();
},
lock: function() {
this.erase();
},
place: function() {
if (!this.obj.bIsLocked) {
this.erase();
this._render();
this.draw();
}
},
_draw: function() {
Element.prototype.draw.call(this);
},
_render: function() {
var container=document.createElement('div');
container.setAttribute('id', this.obj.conf.object_id+'-controls');
this.dom_obj = container;
var x=this.obj.parseCoords(this.obj.conf.x, 'x');
var y=this.obj.parseCoords(this.obj.conf.y, 'y');
var size=10;
for (var i=0, l = x.length; i < l; i++)
this.renderDragger(i, x[i], y[i], - size / 2, - size / 2, size);
if (this.hasTwoParts())
this.renderMidToggle(x.length+2,
this.obj.getLineMid(this.obj.conf.x, 'x'),
this.obj.getLineMid(this.obj.conf.y, 'y'),
20 - size / 2,
-size / 2 + 5,
size);
},
hasTwoParts: function() {
return this.obj.conf.view_type === 'line'
&& (this.obj.conf.line_type == 10
|| this.obj.conf.line_type == 13
|| this.obj.conf.line_type == 14
|| this.obj.conf.line_type == 15);
},
renderDragger: function (num, objX, objY, offX, offY, size) {
var ctl=document.createElement('div');
this.dom_obj.appendChild(ctl);
ctl.setAttribute('id', this.obj.conf.object_id+'-drag-' + num);
ctl.className = 'control drag';
ctl.title          = 'Move object';
ctl.style.zIndex   = parseInt(this.obj.conf.z)+1;
ctl.style.width    = addZoomFactor(size) + 'px';
ctl.style.height   = addZoomFactor(size) + 'px';
ctl.style.left     = (objX + offX) + 'px';
ctl.style.top      = (objY + offY) + 'px';
ctl.objOffsetX     = offX;
ctl.objOffsetY     = offY;
var img=document.createElement('img');
img.src = '../../frontend/nagvis-js/images/internal/control_drag.png';
img.style.width    = addZoomFactor(size) + 'px';
img.style.height   = addZoomFactor(size) + 'px';
ctl.appendChild(img);
makeDragable(ctl, this.obj, this.obj.saveObject, this.obj.moveObject);
},
renderMidToggle: function (num, objX, objY, offX, offY, size) {
var ctl=document.createElement('div');
this.dom_obj.appendChild(ctl);
ctl.setAttribute('id', this.obj.conf.object_id+'-togglemid-' + num);
ctl.className = 'control togglemid';
if (this.obj.bIsLocked)
ctl.title = 'Unlock line middle';
else
ctl.title = 'Lock line middle';
ctl.style.zIndex   = parseInt(this.obj.conf.z)+1;
ctl.style.width    = addZoomFactor(size) + 'px';
ctl.style.height   = addZoomFactor(size) + 'px';
ctl.style.left     = (objX + offX) + 'px';
ctl.style.top      = (objY + offY) + 'px';
ctl.objOffsetX     = offX;
ctl.objOffsetY     = offY;
var img=document.createElement('img');
if (this.isMidLocked())
img.src = '../../frontend/nagvis-js/images/internal/control_locked.png';
else
img.src = '../../frontend/nagvis-js/images/internal/control_unlocked.png';
img.style.width    = addZoomFactor(size) + 'px';
img.style.height   = addZoomFactor(size) + 'px';
ctl.appendChild(img);
addEvent(ctl, 'click', function(element_obj) {
return function(event) {
event = event || window.event;
element_obj.toggleMidLock();
contextHide();
return preventDefaultEvents(event);
};
}(this));
ctl = null;
},
isMidLocked: function() {
return this.obj.conf.x.split(',').length == 2;
},
toggleMidLock: function() {
var x=this.obj.conf.x.split(',');
var y=this.obj.conf.y.split(',')
if (this.isMidLocked()) {
this.obj.conf.x = [
x[0],
middle(this.obj.parseCoords(this.obj.conf.x, 'x', false)[0], this.obj.parseCoords(this.obj.conf.x, 'x', false)[1], this.obj.conf.line_cut),
x[1],
].join(',');
this.obj.conf.y = [
y[0],
middle(this.obj.parseCoords(this.obj.conf.y, 'y', false)[0], this.obj.parseCoords(this.obj.conf.y, 'y', false)[1], this.obj.conf.line_cut),
y[1],
].join(',');
} else {
this.obj.conf.x = [ x[0], x[2] ].join(',');
this.obj.conf.y = [ y[0], y[2] ].join(',');
}
var parts=g_view.unproject(this.obj.conf.x.toString().split(','),
this.obj.conf.y.toString().split(','));
var x=parts[0].join(',');
var y=parts[1].join(',');
saveObjectAttr(this.obj.conf.object_id, {'x': x, 'y': y});
this.obj.render();
}
});
var ElementLine=Element.extend({
line_container : null,
parts          : null,
canvas         : null,
perfdata       : null,
link_area      : null,
constructor: function(obj) {
this.parts = [];
this.base(obj);
},
update: function() {
new ElementLineControls(this.obj).addTo(this.obj);
},
updateAttrs: function(only_state) {
if (!only_state || (this.isWeathermapLine() &&
(this.obj.stateChanged() || this.obj.outputOrPerfdataChanged()))) {
this.redrawLine();
}
},
render: function() {
if (this.isWeathermapLine())
this.parsePerfdata();
var container=document.createElement('div');
container.setAttribute('id', this.obj.conf.object_id+'-linediv');
container.className = 'line';
this.dom_obj = container;
var oLineDiv=document.createElement('div');
this.line_container = oLineDiv;
container.appendChild(oLineDiv);
oLineDiv.setAttribute('id', this.obj.conf.object_id+'-line');
oLineDiv.style.zIndex = parseInt(this.obj.conf.z)-1;
this.calcLineParts();
this.renderLine();
this.renderActionContainer();
this.renderLinkArea();
this.renderLabels();
},
place: function() {
this.redrawLine();
},
unlock: function() {
this.toggleActionContainer();
},
lock: function() {
this.toggleActionContainer();
},
redrawLine: function() {
var trigger_obj=this.obj.trigger_obj;
trigger_obj.parentNode.removeChild(trigger_obj);
this.clearActionContainer();
this.erase();
this.obj.trigger_obj = trigger_obj;
this.render();
this.draw();
},
renderActionContainer: function() {
if (!this.obj.trigger_obj) {
var oLink=document.createElement('a');
oLink.setAttribute('id', this.obj.conf.object_id+'-linelink');
oLink.className = 'linelink';
this.obj.trigger_obj = oLink;
} else {
var oLink=this.obj.trigger_obj;
this.clearActionContainer();
}
this.dom_obj.appendChild(oLink);
if (this.obj.conf.url) {
oLink.href = this.obj.conf.url;
oLink.target = this.obj.conf.url_target;
} else {
oLink.href = 'javascript:void(0)';
}
},
clearActionContainer: function() {
while (this.obj.trigger_obj.firstChild)
this.obj.trigger_obj.removeChild(this.obj.trigger_obj.firstChild);
},
toggleActionContainer: function() {
if (!this.obj.needsLineHoverArea())
this.obj.trigger_obj.style.display = 'none';
else
this.obj.trigger_obj.style.display = 'block';
},
calcLineParts: function() {
this.parts = [];
var x=this.obj.parseCoords(this.obj.conf.x, 'x');
var y=this.obj.parseCoords(this.obj.conf.y, 'y');
for (var i=0; i < x.length; i++) {
x[i] = parseInt(x[i], 10);
y[i] = parseInt(y[i], 10);
}
var xStart=x[0];
var yStart=y[0];
var xEnd=x[x.length - 1];
var yEnd=y[y.length - 1];
var width=addZoomFactor(this.obj.conf.line_width);
if (width <= 0)
width = 1; // minimal width for lines
var cut=this.obj.conf.line_cut;
switch (this.obj.conf.line_type) {
case '11': // ---> lines
this.renderArrow(0, xStart, yStart, xEnd, yEnd, width);
break;
case '12': // --- lines
this.renderSimpleLine(0, xStart, yStart, xEnd, yEnd, width);
break;
case '10':
case '13':
case '14':
case '15':
if (x.length == 2) {
var xMid=middle(xStart, xEnd, cut);
var yMid=middle(yStart, yEnd, cut);
} else {
var xMid=x[1];
var yMid=y[1];
}
this.renderArrow(0, xStart, yStart, xMid, yMid, width);
this.renderArrow(1, xEnd, yEnd, xMid, yMid, width);
break;
default:
alert('Error: Unknown line type');
}
},
calcColors: function(id) {
var color='#FFCC66';
var border_color='#000000';
switch (this.obj.conf.summary_state) {
case 'UNREACHABLE':
case 'DOWN':
case 'CRITICAL':
case 'WARNING':
case 'UNKNOWN':
case 'ERROR':
case 'UP':
case 'OK':
case 'PENDING':
color = oStates[this.obj.conf.summary_state].color;
break;
}
if (this.isWeathermapLine())
color = this.calcWeathermapColor(id);
if (this.obj.conf.summary_problem_has_been_acknowledged === 1
|| this.obj.conf.summary_in_downtime === 1
|| this.obj.conf.summary_stale) {
color = lightenColor(color, 100, 100, 100);
}
return [color, border_color];
},
isWeathermapLine: function() {
return this.obj.conf.line_type == 13 || this.obj.conf.line_type == 14
|| this.obj.conf.line_type == 15;
},
renderLine: function() {
var allX=[], allY = [];
for (var i=0, len = this.parts.length; i < len; i++) {
allX = allX.concat(this.parts[i][2]);
allY = allY.concat(this.parts[i][3]);
}
var xMin=min(allX);
var yMin=min(allY);
var xMax=max(allX);
var yMax=max(allY);
var border=5;
var canvas=document.createElement('canvas');
this.canvas = canvas;
if (!canvas.getContext)
return; // FIXME: Show an error message?
canvas.setAttribute('id', this.obj.conf.object_id+'-canvas');
canvas.style.position = 'absolute';
this.line_container.appendChild(canvas);
canvas.style.left = (xMin-border)+"px";
canvas.style.top = (yMin-border)+"px";
canvas.width = Math.round(xMax-xMin)+2*border;
canvas.height = Math.round(yMax-yMin)+2*border;
canvas.style.zIndex = parseInt(this.obj.conf.z)-1;
addEvent(canvas, 'mousemove', this.handleMouseMove.bind(this));
var ctx=canvas.getContext('2d');
if (!ctx)
return; // silently skip
var devicePixelRatio=window.devicePixelRatio || 1;
var backingStoreRatio=ctx.webkitBackingStorePixelRatio ||
ctx.mozBackingStorePixelRatio ||
ctx.msBackingStorePixelRatio ||
ctx.oBackingStorePixelRatio ||
ctx.backingStorePixelRatio || 1;
var ratio=devicePixelRatio / backingStoreRatio;
if (devicePixelRatio !== backingStoreRatio) {
var oldWidth=canvas.width;
var oldHeight=canvas.height;
canvas.width = oldWidth * ratio;
canvas.height = oldHeight * ratio;
canvas.style.width = oldWidth + 'px';
canvas.style.height = oldHeight + 'px';
ctx.scale(ratio, ratio);
}
ctx.clearRect(0, 0, canvas.width, canvas.height);
var part;
for (var i=0, len = this.parts.length; i < len; i++) {
part = this.parts[i];
ctx.fillStyle = part[4][0];
ctx.beginPath();
ctx.moveTo(part[2][0]-xMin+border, part[3][0]-yMin+border);
for (var a=1, len2 = part[2].length; a < len2; a++)
ctx.lineTo(part[2][a]-xMin+border, part[3][a]-yMin+border);
ctx.fill();
ctx.lineWidth = 1;
ctx.strokeStyle = part[4][1];
ctx.stroke();
}
},
renderArrow: function(id, x1, y1, x2, y2, w) {
var xCoord=[
x1 + newX(x2-x1, y2-y1, 0, w),
x2 + newX(x2-x1, y2-y1, -4*w, w),
x2 + newX(x2-x1, y2-y1, -4*w, 2*w),
x2,
x2 + newX(x2-x1, y2-y1, -4*w, -2*w),
x2 + newX(x2-x1, y2-y1, -4*w, -w),
x1 + newX(x2-x1, y2-y1, 0, -w),
x1 + newX(x2-x1, y2-y1, 0, w)
];
var yCoord=[
y1 + newY(x2-x1, y2-y1, 0, w),
y2 + newY(x2-x1, y2-y1, -4*w, w),
y2 + newY(x2-x1, y2-y1, -4*w, 2*w),
y2,
y2 + newY(x2-x1, y2-y1, -4*w, -2*w),
y2 + newY(x2-x1, y2-y1, -4*w, -w),
y1 + newY(x2-x1, y2-y1, 0, -w),
y1 + newY(x2-x1, y2-y1, 0, w)
];
this.renderLinePart(id, [x1, y1], [x2, y2], xCoord, yCoord);
},
renderSimpleLine: function(id, x1, y1, x2, y2, w) {
var xCoord=[
x1 + newX(x2-x1, y2-y1, 0, w),
x2 + newX(x2-x1, y2-y1, w, w),
x2 + newX(x2-x1, y2-y1, w, -w),
x1 + newX(x2-x1, y2-y1, 0, -w),
x1 + newX(x2-x1, y2-y1, 0, w)
];
var yCoord=[
y1 + newY(x2-x1, y2-y1, 0, w),
y2 + newY(x2-x1, y2-y1, w, w),
y2 + newY(x2-x1, y2-y1, w, -w),
y1 + newY(x2-x1, y2-y1, 0, -w),
y1 + newY(x2-x1, y2-y1, 0, w)
];
this.renderLinePart(id, [x1, y1], [x2, y2], xCoord, yCoord);
},
renderLinePart: function(id, start, end, x, y) {
this.parts.push([start, end, x, y, this.calcColors(id)]);
},
handleMouseMove: function(event) {
event = event || window.event;
if (getTargetRaw(event).tagName !== 'CANVAS')
return true;
var scrollTop=document.body.scrollTop ? document.body.scrollTop :
document.documentElement.scrollTop;
var scrollLeft=document.body.scrollLeft ? document.body.scrollLeft :
document.documentElement.scrollLeft;
var x=event.clientX - getSidebarWidth() + scrollLeft;
var y=event.clientY - getHeaderHeight() + scrollTop;
var pnpoly=function(nvert, vertx, verty, testx, testy) {
var i, j, c = false;
for ( i = 0, j = nvert-1; i < nvert; j = i++ ) {
if ( ( ( verty[i] > testy ) != ( verty[j] > testy ) ) &&
( testx < ( vertx[j] - vertx[i] ) * ( testy - verty[i] ) / ( verty[j] - verty[i] ) + vertx[i] ) ) {
c = !c;
}
}
return c;
};
var part=null,
over = false;
for (var i=0, len = this.parts.length; i < len; i++) {
part = this.parts[i];
if (pnpoly(part[2].length, part[2], part[3], x, y)) {
over = true;
break;
}
}
if (over) {
add_class(this.canvas, 'active');
this.link_area.style.display = '';
this.link_area.style.left = (x-5) + 'px';
this.link_area.style.top = (y-5) + 'px';
if (usesSource('worldmap'))
this.obj.marker._bringToFront();
} else {
remove_class(this.canvas, 'active');
this.link_area.style.display = 'none';
if (usesSource('worldmap'))
this.obj.marker._resetZIndex();
}
},
renderLabels: function() {
if (!this.isWeathermapLine())
return; // Only weathermap lines have labels at the moment
if (!this.obj.conf.line_label_show || this.obj.conf.line_label_show !== '1')
return; // skip over when labels are disabled
var cutIn=this.obj.conf.line_label_pos_in;
var cutOut=this.obj.conf.line_label_pos_out;
var yOffset=parseInt(this.obj.conf.line_label_y_offset);
this.renderLabel(0);
this.renderLabel(1);
},
getLabelWidth: function(str) {
if(str && str.length > 0)
return (str.length / 2) * 9;
else
return 10;
},
renderLabel: function(id) {
var x1=this.parts[id][0][0],
y1 = this.parts[id][0][1],
x2 = this.parts[id][1][0],
y2 = this.parts[id][1][1];
var cut=id == 0 ? this.obj.conf.line_label_pos_in
: this.obj.conf.line_label_pos_out;
var x=middle(x1, x2, cut),
y = middle(y1, y2, cut);
if (this.perfdata === null)
return;
var txt=this.perfdata[id][1] + this.perfdata[id][2];
if (this.obj.conf.line_type == 15)
txt = this.perfdata[2+id][1] + this.perfdata[2+id][2];
var labelHeight=21,
labelWidth  = this.getLabelWidth(txt);
this.obj.trigger_obj.appendChild(
renderNagVisTextbox(this.obj.conf.object_id+'-link'+id,
'#ffffff', '#000000', (x-labelWidth), parseInt(y - labelHeight / 2),
this.obj.conf.z, 'auto', 'auto', '<b>' + txt + '</b>'));
if (this.obj.conf.line_type == 14) {
txt = this.perfdata[2+id][1] + this.perfdata[2+id][2];
labelWidth = this.getLabelWidth(txt);
this.obj.trigger_obj.appendChild(
renderNagVisTextbox(this.obj.conf.object_id+'-link'+(id+1),
'#ffffff', '#000000', (x-labelWidth), parseInt(y + labelHeight / 2),
this.obj.conf.z, 'auto', 'auto', '<b>' + txt + '</b>'));
}
},
renderLinkArea: function() {
var div=document.createElement('div');
this.link_area = div;
div.setAttribute('id', this.obj.conf.object_id+'-link');
div.style.position = 'absolute';
div.style.top = '-100px'; // out of screen by default
div.style.zIndex = parseInt(this.obj.conf.z)+1;
div.style.width = '10px';
div.style.height = '10px';
this.obj.trigger_obj.appendChild(div);
},
parsePerfdata: function() {
this.perfdata = null;
var perf=this.parsePerfdataString();
if (!perf) {
this.addWeathermapLineError("Perfdata string is empty");
return;
}
if (!isset(perf[0])) {
this.addWeathermapLineError("Value 1 is empty");
return;
}
if (!isset(perf[1])) {
this.addWeathermapLineError("Value 2 is empty");
return;
}
if (this.obj.conf.line_type == 14 || this.obj.conf.line_type == 15) {
if (!isset(perf[2])) {
this.addWeathermapLineError("Value 3 is empty");
return;
}
if (!isset(perf[3])) {
this.addWeathermapLineError("Value 4 is empty");
return;
}
}
if (perf[0][2] === null || perf[0][2] === ''
|| perf[1][2] === null || perf[1][2] === '') {
perf = this.calculateUsage(perf);
}
this.perfdata = perf;
},
addWeathermapLineError: function(e) {
this.obj.conf.summary_output += ' (Weathermap Line Error: ' + e + ')';
},
calcWeathermapColor: function(id) {
if (!this.perfdata)
return '#FFCC66';
if (this.perfdata[id][2] == '%' && this.perfdata[id][1] !== null) {
return this.getColorFill(this.perfdata[id][1]);
} else {
this.obj.conf.summary_output += ' (Weathermap Line Error: Value '
+ id +' is not a percentage value)';
return '#FFCC66';
}
},
getColorFill: function(perc) {
var ranges=this.obj.conf.line_weather_colors.split(',');
for(var i=0; i < ranges.length; i++) {
var parts=ranges[i].split(':');
if(parseFloat(perc) <= parts[0])
return parts[1];
parts = null;
}
ranges = null;
return '#000000';
},
calculateUsage: function(oldPerfdata) {
var newPerfdata=[];
var foundNew=false;
var display_bits=false;
if(oldPerfdata.length >= 11 && oldPerfdata[10][5] == '0.0')
display_bits = true;
for(var i=0; i < oldPerfdata.length; i++) {
if(oldPerfdata[i][0] == 'in' && (oldPerfdata[i][2] === null || oldPerfdata[i][2] === '')) {
newPerfdata[0] = this.perfdataCalcPerc(oldPerfdata[i]);
if(!display_bits) {
newPerfdata[2] = this.perfdataCalcBytesReadable(oldPerfdata[i]);
} else {
oldPerfdata[i][1] *= 8; // convert those hakish bytes to bits
newPerfdata[2] = this.perfdataCalcBitsReadable(oldPerfdata[i]);
}
foundNew = true;
}
if(oldPerfdata[i][0] == 'out' && (oldPerfdata[i][2] === null || oldPerfdata[i][2] === '')) {
newPerfdata[1] = this.perfdataCalcPerc(oldPerfdata[i]);
if(!display_bits) {
newPerfdata[3] = this.perfdataCalcBytesReadable(oldPerfdata[i]);
} else {
oldPerfdata[i][1] *= 8; // convert those hakish bytes to bits
newPerfdata[3] = this.perfdataCalcBitsReadable(oldPerfdata[i]);
}
foundNew = true;
}
}
if(foundNew)
return newPerfdata;
else
return oldPerfdata;
},
perfdataCalcBitsReadable: function(set) {
var KB=1024;
var MB=1024 * 1024;
var GB=1024 * 1024 * 1024;
if(set[1] > GB) {
set[1] /= GB
set[2]  = 'Gbit/s'
} else if(set[1] > MB) {
set[1] /= MB
set[2]  = 'Mbit/s'
} else if(set[1] > KB) {
set[1] /= KB
set[2]  = 'Kbit/s'
} else {
set[2]  = 'bit/s'
}
set[1] = Math.round(set[1]*100)/100;
return set;
},
perfdataCalcBytesReadable: function(set) {
var KB=1024;
var MB=1024 * 1024;
var GB=1024 * 1024 * 1024;
if(set[1] > GB) {
set[1] /= GB
set[2]  = 'GB/s'
} else if(set[1] > MB) {
set[1] /= MB
set[2]  = 'MB/s'
} else if(set[1] > KB) {
set[1] /= KB
set[2]  = 'KB/s'
} else {
set[2]  = 'B/s'
}
set[1] = Math.round(set[1]*100)/100;
return set;
},
perfdataCalcPerc: function(set) {
if(set[1] === null || set[6] === null || set[1] == '' || set[6] == '')
return set;
return Array(set[0], Math.round(set[1]*100/set[6]*100)/100, '%', set[3], set[4], 0, 100);
},
parsePerfdataString: function() {
var parsed=[];
var perfdata=this.obj.conf.perfdata;
if (!perfdata)
return [];
perfdata = perfdata.replace('/\s*=\s*/', '=');
var re=/([^=]+)=([\d\.\-]+)([\w%]*);?([\d\.\-:~@]+)?;?([\d\.\-:~@]+)?;?([\d\.\-]+)?;?([\d\.\-]+)?\s*/g;
var perfdataMatches=perfdata.match(re);
if (perfdataMatches == null)
return [];
for (var i=0; i < perfdataMatches.length; i++) {
var tmpSetMatches=perfdataMatches[i].match(/(&#145;)?([\w\s\=\']*)(&#145;)?\=([\d\.\-\+]*)([\w%]*)[\;|\s]?([\d\.\-:~@]+)*[\;|\s]?([\d\.\-:~@]+)*[\;|\s]?([\d\.\-\+]*)[\;|\s]?([\d\.\-\+]*)/);
if (tmpSetMatches === null)
continue;
parsed.push([
tmpSetMatches[2], // label
tmpSetMatches[4], // value
tmpSetMatches[5], // UOM
tmpSetMatches[6], // warn
tmpSetMatches[7], // crit
tmpSetMatches[8], // min
tmpSetMatches[9], // max
]);
}
return parsed;
}
});
var ElementGadget=Element.extend({
gadget_type : null,
updateAttrs: function(only_state) {
if (!only_state || (!this.obj.stateChanged() && this.obj.outputOrPerfdataChanged())) {
this.erase();
this.render();
this.draw();
}
},
render: function() {
this.renderGadget();
this.place();
},
unlock: function () {
this.toggleLink(false);
makeDragable(this.dom_obj, this.obj, this.obj.saveObject, this.obj.moveObject);
},
lock: function () {
this.toggleLink(true);
makeUndragable(this.dom_obj);
},
place: function() {
this.dom_obj.style.top  = this.obj.parseCoord(this.obj.conf.y, 'y') + 'px';
this.dom_obj.style.left = this.obj.parseCoord(this.obj.conf.x, 'x') + 'px';
},
requestGadget: function (param_str) {
var data='members='+escape(JSON.stringify(this.obj.conf.members));
return call_ajax(this.obj.conf.gadget_url + param_str, {
method       : "POST",
post_data    : data,
sync         : true,
}).responseText;
},
detectGadgetType: function (param_str) {
var content=this.requestGadget(param_str);
if (content.substring(0, 4) === 'GIF8' || ! /^[\x00-\x7F]*$/.test(content[0]))
this.gadget_type = 'img';
else
this.gadget_type = 'html';
},
renderGadget: function () {
var sParams='name1=' + this.obj.conf.name;
if (this.obj.conf.type == 'service')
sParams += '&name2=' + escapeUrlValues(this.obj.conf.service_description);
sParams += '&type=' + this.obj.conf.type
+ '&object_id=' + this.obj.conf.object_id
+ '&scale=' + escapeUrlValues(this.obj.conf.gadget_scale.toString())
+ '&state=' + this.obj.conf.summary_state
+ '&stateType=' + this.obj.conf.state_type
+ '&ack=' + this.obj.conf.summary_problem_has_been_acknowledged
+ '&downtime=' + this.obj.conf.summary_in_downtime;
if (this.obj.conf.type == 'dyngroup')
sParams += '&object_types=' + this.obj.conf.object_types;
if (this.obj.conf.perfdata && this.obj.conf.perfdata != '')
sParams += '&perfdata=' + this.obj.conf.perfdata.replace(/\&quot\;|\&\#145\;/g,'%22');
if (this.obj.conf.gadget_opts && this.obj.conf.gadget_opts != '')
sParams += '&opts=' + escapeUrlValues(this.obj.conf.gadget_opts.toString());
if (this.obj.conf.gadget_url.indexOf('?') == -1)
sParams = '?' + sParams;
else
sParams = '&' + sParams;
this.detectGadgetType(sParams);
if (this.gadget_type === 'img') {
var oGadget=document.createElement('img');
addZoomHandler(oGadget);
oGadget.src = this.obj.conf.gadget_url + sParams;
var alt=this.obj.conf.type + '-' + this.obj.conf.name;
if (this.obj.conf.type == 'service')
alt += '-'+this.obj.conf.service_description;
oGadget.alt = alt;
} else {
var oGadget=document.createElement('div');
oGadget.innerHTML = this.requestGadget(sParams);
}
oGadget.setAttribute('id', this.obj.conf.object_id + '-icon');
this.obj.trigger_obj = oGadget;
var oIconDiv=document.createElement('div');
this.dom_obj = oIconDiv;
oIconDiv.setAttribute('id', this.obj.conf.object_id + '-icondiv');
oIconDiv.className = 'icondiv';
oIconDiv.style.zIndex   = this.obj.conf.z;
if(this.obj.conf.url && this.obj.conf.url !== '') {
var oIconLink=document.createElement('a');
oIconLink.href = this.obj.conf.url;
oIconLink.target = this.obj.conf.url_target;
oIconLink.appendChild(oGadget);
oIconDiv.appendChild(oIconLink);
} else {
oIconDiv.appendChild(oGadget);
}
}
});
var ElementLabel=Element.extend({
label_text: null,
update: function() {
this.label_text = this.obj.conf.label_text || '';
if (this.label_text && this.label_text !== '') {
var objName;
if (this.obj.conf.type == 'map') {
objName = this.obj.conf.alias;
} else {
objName = this.obj.conf.name;
}
this.label_text = this.label_text.replace(getRegEx('name', '\\[name\\]', 'g'), objName);
this.label_text = this.label_text.replace(getRegEx('alias', '\\[alias\\]', 'g'), this.obj.conf.alias);
if (this.obj.conf.type == 'service') {
this.label_text = this.label_text.replace(getRegEx('service_description', '\\[service_description\\]', 'g'), this.obj.conf.service_description);
}
}
},
updateAttrs: function(only_state) {
if (!only_state || (!this.obj.stateChanged() && this.obj.outputOrPerfdataChanged())) {
this.erase();
this.render();
this.draw();
}
},
render: function() {
this.dom_obj = renderNagVisTextbox(
this.obj.conf.object_id + '-label',
this.obj.conf.label_background, this.obj.conf.label_border,
0, 0, // coords are set by place()
this.obj.conf.z,
this.obj.conf.label_width, '', this.getText(),
this.obj.conf.label_style
);
this.place();
},
unlock: function () {
addEvent(this.dom_obj, 'mouseover', function() {
document.body.style.cursor = 'move';
});
addEvent(this.dom_obj, 'mouseout', function() {
document.body.style.cursor = 'auto';
});
makeDragable(this.dom_obj, this.obj, this.saveLabel, this.dragLabel);
},
lock: function () {
this.dom_obj.onmouseover = null;
this.dom_obj.onmouseout = null;
makeUndragable(this.dom_obj);
},
place: function () {
this.dom_obj.style.left = this.parseLabelCoord('x') + 'px';
this.dom_obj.style.top  = this.parseLabelCoord('y') + 'px';
},
getText: function () {
var text=this.label_text;
if (text && text !== '') {
text = text.replace(getRegEx('output', '\\[output\\]', 'g'), this.obj.conf.output);
if (this.obj.conf.type == 'service' || this.obj.conf.type == 'host') {
text = text.replace(getRegEx('perfdata', '\\[perfdata\\]', 'g'), this.obj.conf.perfdata);
}
}
if (this.obj.conf.label_maxlen > 0 && text.length > this.obj.conf.label_maxlen)
text = text.substr(0, this.obj.conf.label_maxlen - 2) + '...';
return text;
},
dragLabel: function(trigger_obj, obj, event) {
var isRelative=function(coord) {
return coord.toString().match(/^(?:\+|\-|center|bottom)/);
};
var calcNewLabelCoord=function (labelCoord, coord, newCoord) {
if (isRelative(labelCoord)) {
var ret=newCoord - coord;
if(ret >= 0)
return '+' + ret;
return ret;
} else
return newCoord;
};
obj.conf.label_x = calcNewLabelCoord(obj.conf.label_x,
obj.parseCoord(obj.conf.x, 'x', false), trigger_obj.x);
obj.conf.label_y = calcNewLabelCoord(obj.conf.label_y,
obj.parseCoord(obj.conf.y, 'y', false), trigger_obj.y);
if (isRelative(obj.conf.label_x) || isRelative(obj.conf.label_y))
obj.highlight(true);
},
saveLabel: function(trigger_obj, obj, oParent) {
saveObjectAttr(obj.conf.object_id, {
'label_x': obj.conf.label_x,
'label_y': obj.conf.label_y
});
obj.highlight(false);
},
parseLabelCoord: function (dir) {
if (dir === 'x') {
var coord=this.obj.conf.label_x;
if (this.obj.conf.view_type && this.obj.conf.view_type == 'line') {
var obj_coord=this.obj.getLineMid(this.obj.conf.x, 'x');
} else {
var obj_coord=addZoomFactor(this.obj.parseCoords(this.obj.conf.x, 'x', false)[0], true);
}
} else {
var coord=this.obj.conf.label_y;
if (this.obj.conf.view_type && this.obj.conf.view_type == 'line') {
var obj_coord=this.obj.getLineMid(this.obj.conf.y, 'y');
} else {
var obj_coord=addZoomFactor(this.obj.parseCoords(this.obj.conf.y, 'y', false)[0], true);
}
}
if (dir == 'x' && coord && coord.toString() == 'center') {
var diff=parseInt(parseInt(this.dom_obj.clientWidth) - rmZoomFactor(this.obj.getObjWidth())) / 2;
coord = obj_coord - diff;
} else if (dir == 'y' && coord && coord.toString() == 'bottom') {
coord = obj_coord + rmZoomFactor(this.obj.getObjHeight());
} else if (coord && coord.toString().match(/^(?:\+|\-)/)) {
coord = obj_coord + addZoomFactor(parseFloat(coord));
} else if (!coord || coord === '0') {
coord = obj_coord;
} else {
coord = addZoomFactor(coord, true);
}
return coord;
}
});
var ElementShape=Element.extend({
render: function() {
this.renderShape();
this.place();
},
place: function () {
this.dom_obj.style.top  = this.obj.parseCoord(this.obj.conf.y, 'y') + 'px';
this.dom_obj.style.left = this.obj.parseCoord(this.obj.conf.x, 'x') + 'px';
},
unlock: function () {
this.toggleLink(false);
makeDragable(this.dom_obj, this.obj, this.obj.saveObject, this.obj.moveObject);
},
lock: function () {
this.toggleLink(true);
makeUndragable(this.dom_obj);
},
renderShape: function () {
var oIconDiv=document.createElement('div');
this.dom_obj = oIconDiv;
oIconDiv.setAttribute('id', this.obj.conf.object_id+'-icondiv');
oIconDiv.className = 'icondiv';
oIconDiv.style.zIndex = this.obj.conf.z;
var oIcon=document.createElement('img');
this.obj.trigger_obj = oIcon;
oIcon.setAttribute('id', this.obj.conf.object_id+'-icon');
oIcon.className = 'icon';
if (this.obj.conf.icon_size) {
var size=this.obj.conf.icon_size;
if (size.length == 1) {
var w=parseInt(size),
h = parseInt(size);
} else {
var w=parseInt(size[0]),
h = parseInt(size[1]);
}
oIcon.style.width = w + 'px';
oIcon.style.height = h + 'px';
}
var img_url=null;
if (this.obj.conf.icon.match(/^\[(.*)\]$/)) {
img_url = this.obj.conf.icon.replace(/^\[(.*)\]$/, '$1');
} else {
img_url = oGeneralProperties.path_shapes + this.obj.conf.icon;
}
if (img_url.indexOf('?') !== -1) {
img_url += '&_t=' + iNow;
} else {
img_url += '?_t=' + iNow;
}
addZoomHandler(oIcon);
oIcon.src = img_url;
oIcon.alt = this.obj.conf.type;
if (this.obj.conf.url && this.obj.conf.url !== '') {
var oIconLink=document.createElement('a');
oIconLink.href = this.obj.conf.url;
oIconLink.target = this.obj.conf.url_target;
oIconLink.appendChild(oIcon);
oIconDiv.appendChild(oIconLink);
} else {
oIconDiv.appendChild(oIcon);
}
}
});
var ElementBox=Element.extend({
render: function() {
this.dom_obj = renderNagVisTextbox(
this.obj.conf.object_id+'-label',
this.obj.conf.background_color, this.obj.conf.border_color,
0, 0, // coords are set by this.place()
this.obj.conf.z, this.obj.conf.w,
this.obj.conf.h, this.obj.getText(), this.obj.conf.style
);
this.obj.trigger_obj = this.dom_obj;
this.place();
},
unlock: function () {
makeResizeable(this.dom_obj);
makeDragable(this.dom_obj, this.obj, this.obj.saveObject, this.obj.moveObject);
},
lock: function () {
this.dom_obj.style.cursor = '';
makeUndragable(this.dom_obj);
makeUnresizeable(this.dom_obj);
},
place: function () {
this.dom_obj.style.top  = this.obj.parseCoord(this.obj.conf.y, 'y') + 'px';
this.dom_obj.style.left = this.obj.parseCoord(this.obj.conf.x, 'x') + 'px';
}
});
var ElementTile=Element.extend({
render: function() {
this.renderTile();
},
renderTile: function () {
var alt='';
if(this.type == 'service')
alt = this.obj.conf.name+'-'+this.obj.conf.service_description;
else
alt = this.obj.conf.name;
var div=document.createElement('div');
this.dom_obj = div;
this.obj.trigger_obj = div;
div.setAttribute('id', this.obj.conf.object_id);
div.className = 'mapobj '+this.obj.conf.overview_class;
var url=this.obj.conf.overview_url;
div.onclick = function() {
location.href = url;
return false;
};
if(oPageProperties.showmapthumbs == 1)
div.style.height = '200px';
var oLink=document.createElement('a');
oLink.setAttribute('id', this.obj.conf.object_id+'-icon');
oLink.style.display = "block";
oLink.style.width = "100%";
oLink.style.height = "100%";
oLink.href = this.obj.conf.overview_url;
if (this.obj.conf.icon !== null && this.obj.conf.icon !== '') {
var oImg=document.createElement('img');
oImg.className = 'state';
oImg.align = 'right';
oImg.src   = oGeneralProperties.path_iconsets + this.obj.conf.icon;
oImg.style.width = this.obj.conf.icon_size + 'px';
oImg.style.height = this.obj.conf.icon_size + 'px';
oImg.alt   = this.obj.stateText();
oLink.appendChild(oImg);
}
var h3=document.createElement('h3');
h3.appendChild(document.createTextNode(this.obj.conf.alias));
oLink.appendChild(h3);
if(oPageProperties.showmapthumbs == 1 && this.obj.conf.overview_image != '') {
oImg = document.createElement('img');
oImg.style.width = '200px';
oImg.style.height = '150px';
oImg.src = this.obj.conf.overview_image;
oLink.appendChild(oImg);
}
div.appendChild(oLink);
}
});
var View=Base.extend({
id      : null,
dom_obj : null,
sum_obj : null,
objects : null,
constructor: function(id) {
this.id = id;
this.objects = {};
},
update: function(args) {
var show=isset(args.show) ? '&show='+args.show : '';
var data=[];
for (var i=0, len = args.data.length; i < len; i++)
data.push('i[]='+args.data[i]);
call_ajax(oGeneralProperties.path_server+'?mod=' + args.mod + '&act=getObjectStates'
+ show +'&ty=state'+getViewParams() + this.getFileAgeParams(), {
response_handler : this.handleUpdate.bind(this),
method           : "POST",
post_data        : data.join('&')
});
this.handleRepeatEvents();
},
render: function() {
addEvent(window, 'resize', function() { g_view.scaleView() });
addEvent(window, 'scroll', function() { g_view.scaleView() });
this.scaleView();
},
handleUpdate: function(o) {
if (this.blockUpdates) {
eventlog("ajax", "info", "Throwing new object information away since the view is blocked");
return false;
}
if (!o) {
eventlog("ajax", "info", "handleUpdate: got empty object. Terminating.");
return false;
}
if (isset(o['status']) && o['status'] == 'CHANGED') {
var oChanged=o['data'];
for (var key in oChanged) {
if (key == 'maincfg') {
eventlog("worker", "info", "Main configuration file was updated. Need to reload the page");
if (g_worker_id)
window.clearTimeout(g_worker_id);
window.location.reload(true);
return;
} else {
if (g_view.hasUnlocked()) {
eventlog("worker", "info", "Map config updated, but having unlocked objects - not reloading.");
} else {
eventlog("worker", "info", "Map configuration file was updated. Rerendering the map.");
g_view.render();
g_view.updateFileAges(oChanged);
return;
}
}
}
}
if (oLength(g_view.objects) === 0) {
eventlog("worker", "info", "No objects found, reparsing...");
g_view.init();
return;
}
if (o.length > 0)
this.updateObjects(o, true);
},
updateFileAges: function(data) {
for (var key in data)
oFileAges[key] = data[key];
},
updateObjects: function(attrs, only_state) {
var at_least_one_changed=false;
for (var i=0, len = attrs.length; i < len; i++) {
var objectId=attrs[i].object_id;
if (!isset(this.objects[objectId])) {
this.addObject(attrs[i]);
this.renderObject(objectId);
at_least_one_changed = true; // always reload summary state
}
else {
at_least_one_changed &= this.objects[objectId].updateAttrs(attrs[i], only_state);
}
}
if (at_least_one_changed)
this.handleStateChanged();
},
handleStateChanged: function() {},
drawObject: function(obj) {},
eraseObject: function(obj) {},
handleRepeatEvents: function() {
eventlog("worker", "debug", "handleRepeatEvents: Start");
for (var i in this.objects) {
if (this.objects[i].has_state && this.objects[i].event_time_first !== null) {
this.objects[i].checkRepeatEvents();
}
}
eventlog("worker", "debug", "handleRepeatEvents: End");
},
getFileAgeParams: function() {
var addParams='';
if (g_view.type === 'map' && this.id !== false)
addParams = '&f[]=map,' + this.id + ',' + oFileAges[this.id];
return '&f[]=maincfg,maincfg,' + oFileAges['maincfg'] + addParams;
},
getObjectsToUpdate: function() {
eventlog("worker", "debug", "getObjectsToUpdate: Start");
var stateful=[],
stateless = [];
for (var i in this.objects) {
if (this.objects[i].lastUpdate <= iNow - oWorkerProperties.worker_update_object_states) {
if (this.objects[i] instanceof NagVisStatefulObject) {
stateful.push(i);
} else if (this.objects[i].conf.enable_refresh
&& this.objects[i].conf.enable_refresh == '1') {
stateless.push(i);
}
}
}
eventlog("worker", "debug", "getObjectsToUpdate: Stateful: "+stateful.length
+" Stateless: "+stateless.length);
return [stateful, stateless];
},
renderPageBasics: function() {
if (this.sum_obj)
favicon.change(this.getFaviconImage(this.sum_obj.conf));
document.title = oPageProperties.page_title;
if (this.sum_obj)
document.body.style.backgroundColor = this.getBackgroundColor(this.sum_obj.conf);
},
getBackgroundColor: function(oObj) {
if (!oPageProperties.event_background || oPageProperties.event_background != '1')
return oPageProperties.background_color;
var sColor;
if (!oObj.summary_state || oObj.summary_state == 'PENDING'
|| oObj.summary_state == 'OK' || oObj.summary_state == 'UP')
sColor = oPageProperties.background_color;
else {
sColor = oStates[oObj.summary_state].bgcolor;
if (oObj.summary_in_downtime && oObj.summary_in_downtime === 1)
if (isset(oStates[oObj.summary_state]['downtime_bgcolor'])
&& oStates[oObj.summary_state]['downtime_bgcolor'] != '')
sColor = oStates[oObj.summary_state]['downtime_bgcolor'];
else
sColor = lightenColor(sColor, 100, 100, 100);
else if (oObj.summary_problem_has_been_acknowledged
&& oObj.summary_problem_has_been_acknowledged === 1)
if (isset(oStates[oObj.summary_state]['ack_bgcolor'])
&& oStates[oObj.summary_state]['ack_bgcolor'] != '')
sColor = oStates[oObj.summary_state]['ack_bgcolor'];
else
sColor = lightenColor(sColor, 100, 100, 100);
}
return sColor;
},
getFaviconImage: function(oObj) {
var sFavicon;
if (oObj.summary_in_downtime && oObj.summary_in_downtime === 1)
sFavicon = 'downtime';
else if (oObj.summary_problem_has_been_acknowledged
&& oObj.summary_problem_has_been_acknowledged === 1)
sFavicon = 'ack';
else if (oObj.summary_state.toLowerCase() == 'unreachable')
sFavicon = 'down';
else
sFavicon = oObj.summary_state.toLowerCase();
return oGeneralProperties.path_images+'internal/favicon_'+sFavicon+'.png';
},
scaleView: function() {
var header=document.getElementById('header');
var content=this.dom_obj;
if (!content)
return;
var headerSpacer=document.getElementById('headerspacer');
if (header) {
header.style.width = pageWidth() + 'px';
if (headerSpacer) {
headerSpacer.style.height = header.clientHeight + 'px';
headerSpacer = null;
}
}
content.style.top = getHeaderHeight() + 'px';
if (typeof sidebarUpdatePosition == "function") {
sidebarUpdatePosition();
}
},
project: function(x, y) {
return [x, y];
},
unproject: function(x, y) {
return [x, y];
},
});
var ViewMap=View.extend({
type           : 'map',
rendered       : false,
blockUpdates   : false,
num_unlocked   : false,
constructor: function(id) {
this.base(id);
},
init: function() {
if (!usesSource('worldmap')) {
renderZoombar();
addEvent(document, 'mousedown', context_handle_global_mousedown);
}
this.render();
},
update: function() {
var to_update=this.getObjectsToUpdate();
if (to_update[0].length > 0) {
this.base({
mod  : 'Map',
show : this.id,
data : to_update[0]
});
}
this.rerenderStatelessObjects(to_update[1]);
},
render: function() {
this.dom_obj = document.getElementById('map');
oPageProperties.map_name = this.id;
this.blockUpdates = true;
var wasInMaintenance=inMaintenance(false);
if (this.rendered)
this.updateProperties();
if(inMaintenance()) {
this.blockUpdates = false;
return false
} else if(wasInMaintenance === true) {
frontendMessageRemove('maintenance');
}
wasInMaintenance = null;
call_ajax(oGeneralProperties.path_server + '?mod=Map&act=getMapObjects&show='
+ this.id + getViewParams(), {
response_handler : this.handleMapInit.bind(this),
error_handler    : this.handleMapInitError.bind(this)
});
this.rendered = true;
this.base();
},
handleMapInitError: function(status_code, response, handler_data) {
hideStatusMessage();
if (response === null) {
var response={
'type'    : 'error',
'title'   : 'Error: Invalid response',
'message' : 'Got empty response from server (code: ' + status_code + '). '
+ 'Take a look at the web server error log for details.',
};
}
frontendMessage(response, 'serverError');
},
handleMapInit: function(oObjects) {
if (!oObjects) {
hideStatusMessage();
return;
}
for (var i in this.objects) {
var obj=this.objects[i];
if(obj && typeof obj.remove === 'function') {
obj.remove();
if(!obj.bIsLocked)
this.updateNumUnlocked(-1);
delete this.objects[i];
}
}
if (usesSource('worldmap')) {
g_map_objects.clearLayers();
}
eventlog("worker", "info", "Parsing "+this.type+" objects");
this.initializeObjects(oObjects);
if (getViewParam('zoom') == 'fill')
set_fill_zoom_factor();
this.renderMapBasics();
if(oViewProperties && oViewProperties.search && oViewProperties.search != '') {
eventlog("worker", "info", "Searching for matching object(s)");
searchObjects(oViewProperties.search);
}
hideStatusMessage();
this.blockUpdates = false;
},
addObject: function(attrs) {
var obj;
switch (attrs.type) {
case 'host':
obj = new NagVisHost(attrs);
break;
case 'service':
obj = new NagVisService(attrs);
break;
case 'hostgroup':
obj = new NagVisHostgroup(attrs);
break;
case 'servicegroup':
obj = new NagVisServicegroup(attrs);
break;
case 'dyngroup':
obj = new NagVisDynGroup(attrs);
break;
case 'aggr':
obj = new NagVisAggr(attrs);
break;
case 'map':
obj = new NagVisMap(attrs);
break;
case 'textbox':
obj = new NagVisTextbox(attrs);
break;
case 'container':
obj = new NagVisContainer(attrs);
break;
case 'shape':
obj = new NagVisShape(attrs);
break;
case 'line':
obj = new NagVisLine(attrs);
break;
default:
alert('Error: Unknown object type');
return;
break;
}
if (!obj.bIsLocked)
this.updateNumUnlocked(1);
this.objects[obj.conf.object_id] = obj;
},
erase: function() {
for (var i in this.objects) {
this.objects[i].erase();
}
},
renderObject: function(object_id) {
var obj=this.objects[object_id];
obj.update();
obj.render();
if (isset(oViewProperties.event_on_load) && oViewProperties.event_on_load == 1
&& obj.has_state && obj.hasProblematicState()) {
obj.raiseEvents(false);
obj.initRepeatedEvents();
}
var parents=obj.getParentObjectIds();
if (parents) {
for (var parentObjId in parents) {
this.objects[parentObjId].addChild(obj);
}
}
},
drawObject: function(obj) {
this.dom_obj.appendChild(obj.dom_obj);
},
eraseObject: function(obj) {
this.dom_obj.removeChild(obj.dom_obj);
},
initializeObjects: function(aMapObjectConf) {
eventlog("worker", "debug", "initializeObjects: Start setting map objects");
this.sum_obj = new NagVisMap(aMapObjectConf[0]);
for (var i=1, len = aMapObjectConf.length; i < len; i++)
this.addObject(aMapObjectConf[i]);
for (var i in this.objects)
this.renderObject(i);
eventlog("worker", "debug", "initializeObjects: End setting map objects");
},
renderMapBasics: function() {
oPageProperties.page_title = oPageProperties.alias
+ ' (' + this.sum_obj.conf.summary_state + ') :: '
+ oGeneralProperties.internal_title;
this.renderPageBasics();
this.renderBackgroundImage();
},
renderBackgroundImage: function() {
var sImage=oPageProperties.background_image;
if (typeof sImage !== 'undefined' && sImage !== 'none' && sImage !== '') {
var oImage=document.getElementById('backgroundImage');
if (!oImage) {
var oImage=document.createElement('img');
oImage.id = 'backgroundImage';
document.getElementById('map').appendChild(oImage);
}
addZoomHandler(oImage, true);
oImage.src = sImage;
}
},
handleStateChanged: function() {
call_ajax(oGeneralProperties.path_server + '?mod=Map&act=getObjectStates&show='+this.id
+ '&ty=summary' + getViewParams(), {
response_handler : this.handleSumObjUpdate.bind(this)
});
},
handleSumObjUpdate: function(objects) {
this.sum_obj = new NagVisMap(objects[0]);
this.renderMapBasics();
},
updateProperties: function() {
call_ajax(oGeneralProperties.path_server+'?mod=Map&act=getMapProperties&show='
+ escapeUrlValues(this.id)+getViewParams(), {
response_handler : function(props) {
oPageProperties = props;
}
});
},
rerenderStatelessObjects: function(objects) {
for (var i=0, len = objects.length; i < len; i++)
this.objects[objects[i]].render();
},
removeObject: function(object_id) {
var obj=this.objects[object_id];
obj.detachChilds();
saveObjectRemove(object_id);
obj.remove();
if (!obj.bIsLocked)
this.updateNumUnlocked(-1);
delete this.objects[object_id];
},
hasUnlocked: function() {
return this.num_unlocked > 0;
},
toggleObjectLock: function(object_id, lock) {
this.updateNumUnlocked(this.objects[object_id].toggleLock(lock));
},
updateNumUnlocked: function(num) {
this.num_unlocked += num;
if (this.num_unlocked == 0) {
var o=document.getElementById('editIndicator');
if (o)
o.style.display = 'none';
gridRemove();
} else {
var o=document.getElementById('editIndicator');
if (o)
o.style.display = '';
gridParse();
}
}
});
var ViewWorldmap=ViewMap.extend({
constructor: function(id) {
this.base(id);
},
init: function() {
this.initWorldmap();
this.base();
},
drawObject: function(obj) {
var latlng=g_map.containerPointToLatLng(L.point(0, 0));
L.nagVisMarker(latlng, {
icon: L.nagVisObj({node: obj.dom_obj, obj: obj}),
clickable: false,
riseOnHover: obj.conf.view_type !== 'line',
zIndexOffset: obj.conf.view_type === 'line' ? -1 : 0
}).addTo(g_map_objects);
},
eraseObject: function(obj) {},
initWorldmap: function() {
L.Icon.Default.imagePath = oGeneralProperties.path_base+'/frontend/nagvis-js/images/leaflet';
g_map = L.map('map', {
markerZoomAnimation: false,
maxBounds: [ [-85,-180.0], [85,180.0] ],
minZoom: 2
}).setView(getViewParam('worldmap_center').split(','), parseInt(getViewParam('worldmap_zoom')));
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
attribution: '&copy; <a href="http://www.openstreetmap.org/copyright">OpenStreetMap</a>',
noWrap: true, // don't repeat the world on horizontal axe
detectRetina: true, // look nice on high resolution screens
}).addTo(g_map);
g_map_objects = L.layerGroup().addTo(g_map);
g_map.on('zoomstart', this.handleMoveStart.bind(this));
g_map.on('moveend', this.handleMoveEnd.bind(this));
g_map.on('mousedown', checkHideMenu);
g_map.on('mousedown', context_handle_global_mousedown);
},
handleMoveStart: function(lEvent) {
this.erase();
},
handleMoveEnd: function(lEvent) {
var ll=g_map.getCenter();
setViewParam('worldmap_center', ll.lat+','+ll.lng);
setViewParam('worldmap_zoom', g_map.getZoom());
this.render(); // re-render the whole map
},
saveView: function() {
call_ajax(oGeneralProperties.path_server+'?mod=Map&act=modifyObject&map='
+ this.id + '&type=global&id=0'
+ '&worldmap_center='+getViewParam('worldmap_center')
+ '&worldmap_zoom='+getViewParam('worldmap_zoom'));
},
scaleToAll: function() {
call_ajax(oGeneralProperties.path_server+'?mod=Map&act=getWorldmapBounds'
+ '&show=' + this.id, {
response_handler: this.handleScaleToAll.bind(this),
});
},
handleScaleToAll: function(data) {
g_map.fitBounds(data);
},
project: function(lat, lng) {
var new_coord, x = [], y = [];
for (var i=0; i < lat.length; i++) {
if (isRelativeCoord(lat[i]) || isRelativeCoord(lng[i])) {
x.push(lat[i]);
y.push(lng[i]);
} else {
new_coord = g_map.latLngToContainerPoint(L.latLng(parseFloat(lat[i]), parseFloat(lng[i])));
x.push(new_coord.x);
y.push(new_coord.y);
}
}
return [x, y];
},
unproject: function(x, y) {
if (typeof x !== 'object') {
x = [x];
y = [y];
}
var latlng, lat = [], lng = [];
for (var i=0, l = x.length; i < l; i++) {
if (isRelativeCoord(x[i]) || isRelativeCoord(y[i])) {
lat[i] = x[i];
lng[i] = y[i];
} else {
latlng = g_map.containerPointToLatLng(L.point(x[i], y[i]));
lat[i] = latlng.lat;
lng[i] = latlng.lng;
}
}
return [lat, lng];
}
});
L.NagVisObj = L.Icon.extend({
options: {
iconSize: [0, 0],
iconAnchor: [0, 0],
className: 'leaflet-nagvis-obj',
node: null,
obj: null,
},
createIcon: function (oldIcon) {
var div=(oldIcon && oldIcon.tagName === 'DIV') ? oldIcon : document.createElement('div'),
options = this.options;
for(var i=div.childNodes.length; i > 0; i--)
div.removeChild(div.childNodes[0]);
if (options.node !== null) {
div.appendChild(options.node);
}
this._setIconStyles(div, 'icon');
this._applyOffset();
return div;
},
_applyOffset: function() {
var offset=L.point(this.options.iconSize);
offset._divideBy(2);
this.options.obj.trigger_obj.style.marginLeft = (-offset.x) + 'px';
this.options.obj.trigger_obj.style.marginTop  = (-offset.y) + 'px';
},
createShadow: function () {
return null;
}
});
L.nagVisObj = function (options) {
return new L.NagVisObj(options);
};
L.NagVisMarker = L.Marker.extend({
initialize: function (latlng, options) {
L.Marker.prototype.initialize.call(this, latlng, options);
var obj=options.icon.options.obj;
obj.marker = this;
if (obj.conf.view_type !== 'line') {
addEvent(obj.dom_obj, 'mousedown', function(event) {
event = event || window.event;
if (getButton(event) == 'LEFT')
return preventDefaultEvents(event);
});
}
this.on('add', this._onAdd, this);
},
_onAdd: function(lEvent) {
var icon=this.options.icon,
obj = icon.options.obj,
trigger_obj = icon.options.obj.trigger_obj,
w = trigger_obj.clientWidth,
h = trigger_obj.clientHeight;
icon.options.iconSize = [w, h];
icon._applyOffset();
},
});
L.nagVisMarker = function (ll, options) {
return new L.NagVisMarker(ll, options);
};
var ViewOverview=View.extend({
type           : 'overview',
rendered_maps  : 0,
processed_maps : 0,
constructor: function() {
this.base(null);
},
init: function() {
addEvent(document, 'mousedown', context_handle_global_mousedown);
this.renderPageBasics();
this.render();
this.loadMaps();
this.loadRotations();
},
update: function() {
var to_update=this.getObjectsToUpdate();
if (to_update[0].length > 0) {
this.base({
mod  : 'Overview',
data : to_update[0]
});
}
},
render: function() {
this.dom_obj = document.getElementById('overview');
var types=[
[ oPageProperties.showmaps,      'overviewMaps',      oPageProperties.lang_mapIndex ],
[ oPageProperties.showrotations, 'overviewRotations', oPageProperties.lang_rotationPools ]
];
for (var i=0; i < types.length; i++) {
if (types[i][0] === 1) {
var h2=document.createElement('h2');
h2.innerHTML = types[i][2];
this.dom_obj.appendChild(h2);
var container=document.createElement('div');
container.setAttribute('id', types[i][1]);
container.className = 'infobox';
this.dom_obj.appendChild(container);
}
}
this.base();
},
addMap: function(objects, data) {
var map_name=data[0],
worldmap_has_bbox  = data[1];
this.processed_maps += 1;
if (objects === null || objects.length != 1)  {
eventlog("worker", "warning", "addOverviewMap: Invalid call - maybe broken ajax response ("+map_name+")");
if (this.processed_maps == g_map_names.length)
finishOverviewMaps();
return false;
}
var map_conf=objects[0];
if (!worldmap_has_bbox && map_conf['sources']
&& map_conf['sources'].indexOf('worldmap') !== -1) {
var worldmap=L.map('overview', {
markerZoomAnimation: false,
maxBounds: [ [-85,-180.0], [85,180.0] ],
minZoom: 2
}).setView(map_conf['worldmap_center'].split(','), parseInt(map_conf['worldmap_zoom']));
worldmap.remove();
var overview=document.getElementById('overview');
remove_class(overview, 'leaflet-container');
remove_class(overview, 'leaflet-retina');
remove_class(overview, 'leaflet-fade-anim');
this.processed_maps -= 1;
call_ajax(oGeneralProperties.path_server+'?mod=Overview&act=getObjectStates'
+ '&i[]=map-' + escapeUrlValues(map_name)
+ getViewParams({'bbox': worldmap.getBounds().toBBoxString()}), {
response_handler : this.addMap.bind(this),
handler_data     : [ map_name, true ]
});
return;
}
this.rendered_maps += 1; // also count errors
var container=document.getElementById('overviewMaps');
var mapdiv=null;
var child=null;
for (var i=0; i < container.childNodes.length; i++) {
child = container.childNodes[i];
if (child.id == map_name) {
mapdiv = child;
break;
}
}
var obj=new NagVisMap(map_conf);
this.objects[obj.conf.object_id] = obj;
obj.update();
obj.render();
container.replaceChild(obj.dom_obj, mapdiv);
if (this.processed_maps == g_map_names.length)
this.finishMaps();
},
finishMaps: function() {
hideStatusMessage();
},
addRotations: function(rotations) {
if (oPageProperties.showrotations === 1 && rotations.length > 0) {
for (var i=0, len = rotations.length; i < len; i++) {
new NagVisRotation(rotations[i]).parseOverview();
}
} else {
var container=document.getElementById('overviewRotations');
if (container) {
container.style.display = 'none';
}
}
},
loadMaps: function() {
var map_container=document.getElementById('overviewMaps');
if (oPageProperties.showmaps !== 1 || g_map_names.length == 0) {
if (map_container)
map_container.parentNode.style.display = 'none';
hideStatusMessage();
return false;
}
for (var i=0, len = g_map_names.length; i < len; i++) {
var mapdiv=document.createElement('div');
mapdiv.setAttribute('id', g_map_names[i])
map_container.appendChild(mapdiv);
call_ajax(oGeneralProperties.path_server+'?mod=Overview&act=getObjectStates'
+ '&i[]=map-' + escapeUrlValues(g_map_names[i]) + getViewParams(), {
response_handler : this.addMap.bind(this),
handler_data     : [ g_map_names[i], false ]
});
}
},
loadRotations: function() {
call_ajax(oGeneralProperties.path_server+'?mod=Overview&act=getOverviewRotations', {
response_handler: this.addRotations.bind(this)
});
}
});
var ViewUrl=View.extend({
type: 'url',
constructor: function(id) {
this.base(id);
},
init: function() {
this.render();
hideStatusMessage();
},
update: function() {
this.render();
},
render: function() {
var url=oPageProperties.url;
this.dom_obj = document.getElementById('url');
if (this.dom_obj.tagName == 'DIV') {
call_ajax(oGeneralProperties.path_server + '?mod=Url&act=getContents&show='
+ escapeUrlValues(url), {
response_handler: function(response) {
this.dom_obj.innerHTML = response.content;
}.bind(this),
});
}
else {
this.dom_obj.src = url;
}
this.base();
}
});
var NagVisObject=Base.extend({
dom_obj:               null,
trigger_obj:           null,
visible:               false, // currently shown on the map?
conf:                  null,
lastUpdate:            null,
firstUpdate:           null,
bIsFlashing:           false,
bIsLocked:             true,
childs:                null,
elements:              null,
constructor: function(conf) {
this.setLastUpdate();
this.childs      = [];
this.elements    = [];
this.conf        = conf;
if (this.conf.x) // exclude map summary object
this.transformCoordinates();
if (this.conf.object_id == null)
this.conf.object_id = getRandomLowerCaseLetter() + getRandom(1, 99999);
this.loadLocked();
this.loadViewOpts();
},
update: function() {
if (this.needsContextMenu())
new ElementContext(this).addTo(this);
if (this.needsHoverMenu())
new ElementHover(this).addTo(this);
if (this.conf.label_show && this.conf.label_show == '1')
new ElementLabel(this).addTo(this);
for (var i=0; i < this.elements.length; i++)
this.elements[i].update();
},
updateAttrs: function(attrs, only_state) {
for (var key in attrs)
if (key != 'object_id')
this.conf[key] = attrs[key];
if (!only_state) {
this.transformAttributes();
this.transformCoordinates();
}
for (var i=0; i < this.elements.length; i++)
this.elements[i].updateAttrs(only_state, this.bIsLocked);
if (!only_state)
g_view.drawObject(this);
this.setLastUpdate();
},
transformAttributes: function() {},
render: function () {
this.erase();
var container=document.createElement('div');
container.setAttribute('id', this.conf.object_id);
this.dom_obj = container;
for (var i=0; i < this.elements.length; i++) {
this.elements[i].render();
}
if (!this.bIsLocked) {
for (var i=0; i < this.elements.length; i++) {
this.elements[i].unlock();
}
}
this.draw();
g_view.drawObject(this);
},
draw: function() {
for (var i=0; i < this.elements.length; i++)
this.elements[i].draw(this);
this.visible = true;
},
erase: function () {
if (!this.visible)
return;
for (var i=0; i < this.elements.length; i++)
this.elements[i].erase(this);
g_view.eraseObject(this);
this.visible = false;
},
remove: function() {
this.erase();
},
addElement: function(obj) {
if(this.elements.indexOf(obj) === -1)
this.elements.push(obj);
obj = null;
},
removeElement: function(obj) {
this.elements.splice(this.elements.indexOf(obj), 1);
obj = null;
},
loadLocked: function() {
if (g_view.type != 'map')
return;
if (!oUserProperties.hasOwnProperty('unlocked-' + oPageProperties.map_name))
return;
if (oViewProperties.hasOwnProperty('edit_mode') && oViewProperties['edit_mode'] === true) {
this.bIsLocked = false;
return;
}
var unlocked=oUserProperties['unlocked-' + oPageProperties.map_name].split(',');
this.bIsLocked = unlocked.indexOf(this.conf.object_id) === -1 && unlocked.indexOf('*') === -1;
},
loadViewOpts: function() {
if(this.conf.type == 'line')
return;
if(isset(oViewProperties) && isset(oViewProperties.hover_menu))
this.conf.hover_menu = oViewProperties.hover_menu;
if(isset(oViewProperties) && isset(oViewProperties.context_menu))
this.conf.context_menu = oViewProperties.context_menu;
},
setLastUpdate: function() {
this.lastUpdate = iNow;
if(this.firstUpdate === null)
this.firstUpdate = this.lastUpdate;
},
transformCoordinates: function() {
var converted=g_view.project(
this.conf.x.toString().split(','),
this.conf.y.toString().split(','));
this.conf.x = converted[0].join(',');
this.conf.y = converted[1].join(',');
},
getLineMid: function(coord, dir) {
var c=coord.split(',');
if(c.length == 2)
return middle(this.parseCoords(coord, dir)[0],
this.parseCoords(coord, dir)[1],
this.conf.line_cut);
else
return this.parseCoords(coord, dir)[1];
},
toggleLock: function(lock) {
var equal=false;
if(isset(lock) && lock === this.bIsLocked)
equal = true;
if(isset(lock))
this.bIsLocked = lock;
else
this.bIsLocked = !this.bIsLocked;
for (var i=0; i < this.elements.length; i++)
if (this.bIsLocked)
this.elements[i].lock();
else
this.elements[i].unlock();
if (!isset(lock) && (!oViewProperties.hasOwnProperty('edit_mode') || oViewProperties['edit_mode'] !== true)) {
var unlocked=[];
if(oUserProperties.hasOwnProperty('unlocked-' + oPageProperties.map_name))
unlocked = oUserProperties['unlocked-' + oPageProperties.map_name].split(',');
if(this.bIsLocked)
unlocked.splice(unlocked.indexOf(this.conf.object_id), 1);
else
unlocked.push(this.conf.object_id);
storeUserOption('unlocked-' + oPageProperties.map_name, unlocked.join(','));
unlocked = null;
}
if (equal === true)
return 0;
else
return this.bIsLocked ? -1 : 1;
},
getObjLeft: function () {
if (this.conf.x.toString().split(',').length > 1) {
return Math.min.apply(Math, this.parseCoords(this.conf.x, 'x'));
} else {
return this.parseCoord(this.conf.x, 'x');
}
},
getObjTop: function () {
if (this.conf.x.toString().split(',').length > 1) {
return Math.min.apply(Math, this.parseCoords(this.conf.y, 'y'));
} else {
return this.parseCoord(this.conf.y, 'y');
}
},
getObjWidth: function () {
var o=document.getElementById(this.conf.object_id + '-icondiv');
if(o && o.clientWidth)
return parseInt(o.clientWidth);
else
return 0;
},
getObjHeight: function () {
var o=document.getElementById(this.conf.object_id + '-icondiv');
if(o && o.clientHeight)
return parseInt(o.clientHeight);
else
return 0;
},
parseCoord: function(val, dir, addZoom) {
if (addZoom === undefined)
addZoom = true;
var coord=0;
if(!isRelativeCoord(val)) {
coord = parseInt(val);
} else {
if(val.search('%') !== -1) {
var parts=val.split('%');
var objectId=parts[0];
var offset=parts[1];
var refObj=getMapObjByDomObjId(objectId);
if (refObj) {
coord = parseFloat(refObj.parseCoord(refObj.conf[dir], dir, false));
if (addZoom)
coord = addZoomFactor(coord, true);
if (addZoom)
coord += addZoomFactor(parseFloat(offset), false);
else
coord += parseFloat(offset);
return coord;
}
} else {
var refObj=getMapObjByDomObjId(val);
if(refObj)
coord = parseInt(refObj.parseCoord(refObj.conf[dir], dir, false));
}
}
if (addZoom)
return addZoomFactor(coord, true);
else
return coord;
},
parseCoords: function(val, dir, addZoom) {
var l=[];
if(val)
l = val.toString().split(',');
for(var i=0, len = l.length; i < len; i++)
l[i] = this.parseCoord(l[i], dir, addZoom);
return l;
},
makeAbsoluteCoords: function(num) {
var x=num === -1 ? this.conf.x : this.conf.x.split(',')[num];
var y=num === -1 ? this.conf.y : this.conf.y.split(',')[num];
if(!isRelativeCoord(x) && !isRelativeCoord(y))
return;
var xParent=this.getCoordParent(this.conf.x, num);
var yParent=this.getCoordParent(this.conf.y, num);
if(xParent == yParent) {
var o=getMapObjByDomObjId(xParent);
if(o && Object.size(this.getRelativeCoordsUsingParent(xParent)) == 1) {
o.delChild(this);
}
} else {
var o=getMapObjByDomObjId(xParent);
if(o && Object.size(this.getRelativeCoordsUsingParent(xParent)) == 1) {
o.delChild(this);
}
var o=getMapObjByDomObjId(yParent);
if(o && Object.size(this.getRelativeCoordsUsingParent(yParent)) == 1) {
o.delChild(this);
}
}
if(num === -1) {
this.conf.x = this.parseCoord(x, 'x', false);
this.conf.y = this.parseCoord(y, 'y', false);
} else {
var old=this.conf.x.split(',');
old[num] = this.parseCoord(x, 'x', false);
this.conf.x = old.join(',');
old  = this.conf.y.split(',');
old[num] = this.parseCoord(y, 'y', false);
this.conf.y = old.join(',');
}
},
makeRelativeCoords: function(oParent, num) {
var xParent=this.getCoordParent(this.conf.x, num);
var yParent=this.getCoordParent(this.conf.y, num);
var x=num === -1 ? this.conf.x : this.conf.x.split(',')[num];
var y=num === -1 ? this.conf.y : this.conf.y.split(',')[num];
if(isRelativeCoord(x) && isRelativeCoord(y)) {
if(xParent == oParent.conf.object_id
&& yParent == oParent.conf.object_id)
return;
if(xParent != oParent.conf.object_id) {
var o=getMapObjByDomObjId(xParent);
if(o) {
o.delChild(this);
o = null;
}
}
if(yParent != oParent.conf.object_id) {
var o=getMapObjByDomObjId(yParent);
if(o) {
o.delChild(this);
o = null;
}
}
}
oParent.addChild(this);
if(num === -1) {
this.conf.x = this.getRelCoords(oParent, this.parseCoord(this.conf.x, 'x', false), 'x', -1);
this.conf.y = this.getRelCoords(oParent, this.parseCoord(this.conf.y, 'y', false), 'y', -1);
} else {
var newX=this.getRelCoords(oParent, this.parseCoords(this.conf.x, 'x', false)[num], 'x', -1);
var newY=this.getRelCoords(oParent, this.parseCoords(this.conf.y, 'y', false)[num], 'y', -1);
var old=this.conf.x.split(',');
old[num] = newX;
this.conf.x = old.join(',');
old  = this.conf.y.split(',');
old[num] = newY;
this.conf.y = old.join(',');
}
},
getCoordParent: function(val, num) {
var coord=num === -1 ? val.toString() : val.split(',')[num].toString();
return coord.search('%') !== -1 ? coord.split('%')[0] : coord;
},
getRelCoords: function(refObj, val, dir, num) {
var refPos=num === -1 ? refObj.conf[dir] : refObj.conf[dir].split(',')[num];
var offset=parseInt(val) - parseInt(refObj.parseCoord(refPos, dir, false));
var pre=offset >= 0 ? '+' : '';
val        = refObj.conf.object_id + '%' + pre + offset;
refObj     = null;
return val;
},
hasRelativeCoord: function() {
var coords=this.conf.x.toString().split(',').concat(this.conf.y.toString().split(','));
for (var i=0, len = coords.length; i < len; i++)
if (isRelativeCoord(coords[i]))
return true;
return false;
},
calcNewCoord: function(val, dir, num) {
if(!isset(num))
var num=-1;
var oldVal=num === -1 ? this.conf[dir] : this.conf[dir].split(',')[num];
if(isset(oldVal) && isRelativeCoord(oldVal)) {
var objectId=null;
if(oldVal.search('%') !== -1)
objectId = oldVal.split('%')[0];
else
objectId = oldVal;
var refObj=getMapObjByDomObjId(objectId);
if(refObj)
val = this.getRelCoords(refObj, val, dir, -1);
objectId = null;
} else if(num === -1) {
val = Math.round(val);
}
oldVal = null;
if(num === -1) {
return val;
} else {
var old=this.conf[dir].split(',');
if(isRelativeCoord(val))
old[num] = val;
else
old[num] = Math.round(val);
return old.join(',');
}
},
getParentObjectIds: function(num) {
var parentIds={};
if (isset(num)) {
var coords=(this.conf['x'].split(',')[num] + ',' + this.conf['y'].split(',')[num]).split(',');
} else if (isset(this.conf.x) && isset(this.conf.y)) {
var coords=(this.conf.x + ',' + this.conf.y).split(',');
} else {
return parentIds;
}
for(var i=0, len = coords.length; i < len; i++) {
if(isRelativeCoord(coords[i])) {
if(coords[i].search('%') !== -1)
parentIds[coords[i].split('%')[0]] = true;
else if (coords[i])
parentIds[coords[i]] = true;
}
}
coords = null;
return parentIds;
},
getRelativeCoordsUsingParent: function(parentId) {
var matches={};
for(var i=0, len = this.conf.x.split(',').length; i < len; i++) {
if(this.getCoordParent(this.conf.x, i) === parentId && !isset(matches[i]))
matches[i] = true;
else if(this.getCoordParent(this.conf.y, i) === parentId && !isset(matches[i]))
matches[i] = true;
}
return matches;
},
addChild: function(obj) {
if(this.childs.indexOf(obj) === -1)
this.childs.push(obj);
obj = null;
},
delChild: function(obj) {
this.childs.splice(this.childs.indexOf(obj), 1);
obj = null;
},
detachChilds: function() {
for(var i=this.childs.length - 1; i >= 0; i--) {
var nums=this.childs[i].getRelativeCoordsUsingParent(this.conf.object_id);
var obj=this.childs[i];
for(var num in nums) {
obj.makeAbsoluteCoords(num);
}
saveObjectAttr(obj.conf.object_id, {'x': obj.conf.x, 'y': obj.conf.y });
obj  = null;
nums = null;
}
},
parsedX: function() {
return this.parseCoords(this.conf.x, 'x');
},
parsedY: function() {
return this.parseCoords(this.conf.y, 'y');
},
place: function() {
for(var i=0, l = this.elements.length; i < l; i++)
this.elements[i].place();
for(var i=0, l = this.childs.length; i < l; i++)
this.childs[i].place();
},
needsContextMenu: function () {
return (this.conf.context_menu && this.conf.context_menu !== '' && this.conf.context_menu !== '0'
&& this.conf.context_template && this.conf.context_template !== '');
},
needsHoverMenu: function() {
return this.conf.hover_menu && this.conf.hover_menu !== '' && this.conf.hover_menu !== '0'
&& ((this.conf.hover_template && this.conf.hover_template !== '') ||
(this.conf.hover_url && this.conf.hover_url !== ''));
},
needsLink: function() {
return this.conf.url && this.conf.url !== '' && this.conf.url !== '#';
},
needsLineHoverArea: function() {
return this.needsHoverMenu()
|| this.needsContextMenu()
|| this.needsLink()
|| !this.bIsLocked;
},
moveObject: function(trigger_obj, obj) {
var arr=trigger_obj.id.split('-');
var newPos;
if (obj.conf.view_type === 'line') {
newPos = getMidOfAnchor(trigger_obj);
var anchorId=arr[2];
newPos = [ obj.calcNewCoord(newPos[0], 'x', anchorId),
obj.calcNewCoord(newPos[1], 'y', anchorId) ];
var parents=obj.getParentObjectIds(anchorId);
anchorId   = null;
} else {
var offsetX=isset(trigger_obj.objOffsetX) ? trigger_obj.objOffsetX : 0;
var offsetY=isset(trigger_obj.objOffsetY) ? trigger_obj.objOffsetY : 0;
newPos = [ obj.calcNewCoord(trigger_obj.x - offsetX, 'x'),
obj.calcNewCoord(trigger_obj.y - offsetY, 'y') ];
var parents=obj.getParentObjectIds();
}
obj.conf.x = newPos[0];
obj.conf.y = newPos[1];
obj.place();
},
saveObject: function(trigger_obj, obj, oParent) {
var arr=trigger_obj.id.split('-');
if(arr.length > 2)
var anchorId=arr[2];
if (obj.conf.view_type !== 'line')
anchorId = -1;
if (useGrid()) {
if (obj.conf.view_type === 'line') {
var pos=coordsToGrid(obj.parseCoords(obj.conf.x, 'x', false)[anchorId],
obj.parseCoords(obj.conf.y, 'y', false)[anchorId]);
obj.conf.x = obj.calcNewCoord(pos[0], 'x', anchorId);
obj.conf.y = obj.calcNewCoord(pos[1], 'y', anchorId);
} else {
var pos=coordsToGrid(obj.parseCoord(obj.conf.x, 'x', false),
obj.parseCoord(obj.conf.y, 'y', false));
obj.conf.x = obj.calcNewCoord(pos[0], 'x');
obj.conf.y = obj.calcNewCoord(pos[1], 'y');
}
obj.place();
}
if (isset(oParent))
if(oParent !== false)
obj.makeRelativeCoords(oParent, anchorId);
else
obj.makeAbsoluteCoords(anchorId);
var x=obj.conf.x,
y = obj.conf.y;
var parts=g_view.unproject(x.toString().split(','), y.toString().split(','));
x = parts[0].join(',');
y = parts[1].join(',');
saveObjectAttr(obj.conf.object_id, { 'x': x, 'y': y});
},
highlight: function(show) {},
getStatefulMembers: function() {}
});
var NagVisStatefulObject=NagVisObject.extend({
has_state: true,
last_state: null,
members: [],
event_time_first: null,
event_time_last: null,
constructor: function(oConf) {
this.base(oConf);
},
getMembers: function() {
this.members = [];
if(this.conf && this.conf.members && this.conf.members.length > 0) {
for(var i=0, len = this.conf.members.length; i < len; i++) {
var oMember=this.conf.members[i];
var oObj;
switch (oMember.type) {
case 'host':
oObj = new NagVisHost(oMember);
break;
case 'service':
oObj = new NagVisService(oMember);
break;
case 'hostgroup':
oObj = new NagVisHostgroup(oMember);
break;
case 'servicegroup':
oObj = new NagVisServicegroup(oMember);
break;
case 'dyngroup':
oObj = new NagVisDynGroup(oMember);
break;
case 'aggr':
oObj = new NagVisAggr(oMember);
break;
case 'map':
oObj = new NagVisMap(oMember);
break;
case 'textbox':
oObj = new NagVisTextbox(oMember);
break;
case 'container':
oObj = new NagVisContainer(oMember);
break;
case 'shape':
oObj = new NagVisShape(oMember);
break;
case 'line':
oObj = new NagVisLine(oMember);
break;
default:
alert('Error: Unknown member object type ('+oMember.type+')');
break;
}
if(oObj !== null) {
this.members.push(oObj);
}
oObj = null;
oMember = null;
}
}
},
getStatefulMembers: function() {
var stateful=[];
for (var i=0, len = this.members.length; i < len; i++) {
if (this.members[i].has_state) {
stateful.push(this.members[i]);
}
}
return stateful;
},
saveLastState: function() {
this.last_state = {
'summary_state': this.conf.summary_state,
'summary_in_downtime': this.conf.summary_in_downtime,
'summary_stale': this.conf.summary_stale,
'summary_problem_has_been_acknowledged': this.conf.summary_problem_has_been_acknowledged,
'output': this.conf.output,
'perfdata': this.conf.perfdata
};
},
stateChanged: function() {
if(this.conf.summary_state != this.last_state.summary_state ||
this.conf.summary_problem_has_been_acknowledged != this.last_state.summary_problem_has_been_acknowledged ||
this.conf.summary_stale != this.last_state.summary_stale ||
this.conf.summary_in_downtime != this.last_state.summary_in_downtime) {
return true;
} else {
return false;
}
},
stateChangedToWorse: function() {
var lastSubState='normal';
if(this.last_state.summary_problem_has_been_acknowledged && this.last_state.summary_problem_has_been_acknowledged === 1) {
lastSubState = 'ack';
} else if(this.last_state.summary_in_downtime && this.last_state.summary_in_downtime == 1) {
lastSubState = 'downtime';
} else if(this.last_state.summary_stale) {
lastSubState = 'stale';
}
if(!this.last_state.summary_state) {
return true;
}
var lastWeight=oStates[this.last_state.summary_state][lastSubState];
var subState='normal';
if(this.conf.summary_problem_has_been_acknowledged && this.conf.summary_problem_has_been_acknowledged === 1) {
subState = 'ack';
} else if(this.conf.summary_in_downtime && this.conf.summary_in_downtime === 1) {
subState = 'downtime';
} else if(this.conf.summary_stale) {
subState = 'stale';
}
var weight=oStates[this.conf.summary_state][subState];
return lastWeight < weight;
},
hasProblematicState: function() {
if(this.conf.summary_problem_has_been_acknowledged && this.conf.summary_problem_has_been_acknowledged === 1) {
return false;
} else if(this.conf.summary_in_downtime && this.conf.summary_in_downtime === 1) {
return false;
} else if(this.conf.summary_stale && this.conf.summary_stale) {
return false;
}
var weight=oStates[this.conf.summary_state]['normal'];
return weight > oStates['UP']['normal'];
},
outputOrPerfdataChanged: function() {
return this.conf.output != this.last_state.output || this.conf.perfdata != this.last_state.perfdata;
},
update: function () {
this.getMembers();
this.replaceMacros();
if (g_view.type === 'map') {
switch (this.conf.view_type) {
case 'line':
new ElementLine(this).addTo(this);
break;
case 'gadget':
new ElementGadget(this).addTo(this);
break;
default:
new ElementIcon(this).addTo(this);
break;
}
}
this.base();
},
updateAttrs: function(attrs, only_state) {
this.saveLastState();
this.base(attrs, only_state);
this.updateMemberAttrs(attrs, only_state);
if (!only_state) {
this.replaceMacros();
}
if (only_state && this.stateChanged())
this.render(); // erase, rerender and draw object
if (this.stateChanged()) {
if (this.stateChangedToWorse()) {
this.raiseEvents(true);
this.initRepeatedEvents();
}
return true;
}
else {
return false;
}
},
transformAttributes: function() {
this.replaceMacros();
},
updateMemberAttrs: function(attrs, only_state) {
if (!this.members)
return;
for (var i=0, len = attrs.members.length; i < len; i++) {
var member_attrs=attrs.members[i],
updated = false;
for (var a=0, len2 = this.members.length; a < len2; a++) {
var member=this.members[a];
if (member_attrs.object_id == member.conf.object_id) {
member.updateAttrs(member_attrs, only_state);
break;
}
}
}
this.getMembers();
},
raiseEvents: function (stateChanged) {
if (oPageProperties.event_highlight === '1') {
if (this.conf.view_type && this.conf.view_type === 'icon') {
setTimeout(function(obj_id) {
return function() {
flashIcon(obj_id, oPageProperties.event_highlight_duration,
oPageProperties.event_highlight_interval);
};
}(this.conf.object_id), 0);
} else {
}
}
if (oPageProperties.event_scroll === '1') {
setTimeout(function(x, y) {
return function() {
scrollSlow(x, y, 1);
};
}(this.parsedX(), this.parsedY()), 0);
}
if (this.conf.type == 'service') {
if (stateChanged) {
eventlog("state-change", "info", this.conf.type+" "+this.conf.name+" "+this.conf.service_description+": Old: "+this.last_state.summary_state+"/"+this.last_state.summary_problem_has_been_acknowledged+"/"+this.last_state.summary_in_downtime+" New: "+this.conf.summary_state+"/"+this.conf.summary_problem_has_been_acknowledged+"/"+this.conf.summary_in_downtime);
}
else {
eventlog("state-log", "info", this.conf.type+" "+this.conf.name+" "+this.conf.service_description+": State: "+this.conf.summary_state+"/"+this.conf.summary_problem_has_been_acknowledged+"/"+this.conf.summary_in_downtime);
}
}
else {
if (stateChanged) {
eventlog("state-change", "info", this.conf.type+" "+this.conf.name+": Old: "+this.last_state.summary_state+"/"+this.last_state.summary_problem_has_been_acknowledged+"/"+this.last_state.summary_in_downtime+" New: "+this.conf.summary_state+"/"+this.conf.summary_problem_has_been_acknowledged+"/"+this.conf.summary_in_downtime);
}
else {
eventlog("state-log", "info", this.conf.type+" "+this.conf.name+": State: "+this.conf.summary_state+"/"+this.conf.summary_problem_has_been_acknowledged+"/"+this.conf.summary_in_downtime);
}
}
if (oPageProperties.event_sound === '1') {
setTimeout(function(obj_id) {
return function() {
playSound(obj_id, 1);
};
}(this.conf.object_id), 0);
}
},
initRepeatedEvents: function () {
if(isset(oViewProperties.event_repeat_interval)
&& oViewProperties.event_repeat_interval != 0) {
this.event_time_first = iNow;
this.event_time_last  = iNow;
}
},
checkRepeatEvents: function () {
if (!this.hasProblematicState()) {
this.event_time_first = null;
this.event_time_last  = null;
return;
}
if (oViewProperties.event_repeat_duration != -1
&& this.event_time_first
+ oViewProperties.event_repeat_duration < iNow) {
this.event_time_first = null;
this.event_time_last  = null;
return;
}
if (this.event_time_last
+ oViewProperties.event_repeat_interval >= iNow) {
this.raiseEvents(false);
this.event_time_last = iNow;
}
},
replaceMacros: function () {
var name='';
if(this.conf.type == 'service') {
name = 'host_name';
} else {
name = this.conf.type + '_name';
}
if(this.conf.url && this.conf.url !== '') {
if(this.conf.htmlcgi && this.conf.htmlcgi !== '') {
this.conf.url = this.conf.url.replace(getRegEx('htmlcgi', '\\[htmlcgi\\]', 'g'), this.conf.htmlcgi);
} else {
this.conf.url = this.conf.url.replace(getRegEx('htmlcgi', '\\[htmlcgi\\]', 'g'), oGeneralProperties.path_cgi);
}
this.conf.url = this.conf.url.replace(getRegEx('htmlbase', '\\[htmlbase\\]', 'g'), oGeneralProperties.path_base);
this.conf.url = this.conf.url.replace(getRegEx(name, '\\['+name+'\\]', 'g'), this.conf.name);
if(this.conf.type == 'service') {
this.conf.url = this.conf.url.replace(getRegEx('service_description', '\\[service_description\\]', 'g'), this.conf.service_description);
}
if(this.conf.type != 'map') {
this.conf.url = this.conf.url.replace(getRegEx('backend_id', '\\[backend_id\\]', 'g'), this.conf.backend_id);
}
}
},
highlight: function(show) {
if(this.conf.view_type !== 'icon')
return;
var oObjIcon=document.getElementById(this.conf.object_id + '-icon');
var oObjIconDiv=document.getElementById(this.conf.object_id + '-icondiv');
var sColor=oStates[this.conf.summary_state].color;
this.bIsFlashing = show;
if(show) {
oObjIcon.style.border  = "5px solid " + sColor;
oObjIconDiv.style.top  = (this.parseCoord(this.conf.y, 'y') - 5) + 'px';
oObjIconDiv.style.left = (this.parseCoord(this.conf.x, 'x') - 5) + 'px';
} else {
oObjIcon.style.border  = "none";
oObjIconDiv.style.top  = this.parseCoord(this.conf.y, 'y') + 'px';
oObjIconDiv.style.left = this.parseCoord(this.conf.x, 'x') + 'px';
}
sColor      = null;
oObjIconDiv = null;
oObjIcon    = null;
},
});
var NagVisStatelessObject=NagVisObject.extend({
has_state: false,
});
var NagVisHost=NagVisStatefulObject.extend({
constructor: function(oConf) {
this.base(oConf);
}
});
var NagVisService=NagVisStatefulObject.extend({
constructor: function(oConf) {
this.base(oConf);
},
});
var NagVisHostgroup=NagVisStatefulObject.extend({
constructor: function(oConf) {
this.base(oConf);
}
});
var NagVisServicegroup=NagVisStatefulObject.extend({
constructor: function(oConf) {
this.base(oConf);
}
});
var NagVisDynGroup=NagVisStatefulObject.extend({
constructor: function(oConf) {
this.base(oConf);
}
});
var NagVisAggr=NagVisStatefulObject.extend({
constructor: function(oConf) {
this.base(oConf);
}
});
var NagVisMap=NagVisStatefulObject.extend({
update: function () {
if (g_view.type == 'overview')
new ElementTile(this).addTo(this);
this.base();
},
stateText: function () {
var substate='';
if (this.conf.summary_in_downtime == 1)
substate = ' (downtime)';
else if (this.conf.summary_problem_has_been_acknowledged == 1)
substate = ' (ack)';
else if (this.conf.summary_stale)
substate = ' (stale)';
return this.conf.summary_state + substate;
},
});
var NagVisShape=NagVisStatelessObject.extend({
update: function() {
new ElementShape(this).addTo(this);
this.base();
},
});
var NagVisLine=NagVisStatelessObject.extend({
constructor: function(oConf) {
this.base(oConf);
},
update: function() {
var line=new ElementLine(this).addTo(this);
line.calcColors = function(obj) {
return function() {
return [obj.conf.line_color, obj.conf.line_color_border];
};
}(this);
this.base();
},
});
var NagVisTextbox=NagVisStatelessObject.extend({
update: function() {
new ElementBox(this).addTo(this);
this.base();
},
replaceMacros: function (text) {
text = text.replace('[refresh_counter]', '<font id="refreshCounter"></font>');
text = text.replace('[worker_last_run]', '<font id="workerLastRunCounter"></font>');
return text;
},
getText: function() {
return this.replaceMacros(this.conf.text);
}
});
var NagVisContainer=NagVisStatelessObject.extend({
update: function() {
new ElementBox(this).addTo(this);
this.base();
},
render: function () {
this.base();
var span=this.elements[0].dom_obj.childNodes[0];
span.style.display = 'block';
span.style.height = '100%';
if (this.conf.view_type === 'inline') {
call_ajax(this.conf.url, {
response_handler: function(html, span) {
span.innerHTML = html;
},
error_handler: function(status_code, response, span) {
if (status_code === 200)
span.innerHTML = 'Error: '+response;
else
span.innerHTML = 'Error: '+status_code;
},
handler_data : span,
decode_json  : false,
add_ajax_id  : false,
});
} else {
span.innerHTML = '';
var oIframe=document.createElement('iframe');
oIframe.style.borderWidth = 0;
oIframe.style.width  = '100%';
oIframe.style.height = '100%';
oIframe.src = this.conf.url;
span.appendChild(oIframe);
oIframe = null;
}
},
getText: function() {
return '';
}
});
var NagVisRotation=NagVisStatelessObject.extend({
constructor: function(oConf) {
this.base(oConf);
},
parseOverview: function() {
var container=document.getElementById('overviewRotations');
var oTable=document.createElement('table');
oTable.className = 'rotation';
container.appendChild(oTable);
var oTbody=document.createElement('tbody');
oTable.appendChild(oTbody);
var oTr=document.createElement('tr');
var oTd=document.createElement('td');
oTd.className = 'title';
oTd.setAttribute('rowSpan', this.conf.num_steps);
oTd.rowSpan = this.conf.num_steps;
var oLink=document.createElement('a');
oLink.href = this.conf.url;
var h3=document.createElement('h3');
h3.appendChild(document.createTextNode(this.conf.name));
oLink.appendChild(h3);
h3 = null;
oTd.appendChild(oLink);
oTr.appendChild(oTd);
oTd = null;
for(var i=0, len = this.conf.steps.length; i < len; i++) {
if(i !== 0)
oTr = document.createElement('tr');
oTd = document.createElement('td');
oLink = document.createElement('a');
oLink.href = this.conf.steps[i].url;
oLink.appendChild(document.createTextNode(this.conf.steps[i].name));
oTd.appendChild(oLink);
oLink = null;
oTr.appendChild(oTd);
oTd = null;
oTbody.appendChild(oTr);
oTr = null;
}
container = null;
}
});
var g_header_height_cache=null;
var g_worker_id=null;
var g_map=null;
var g_map_objects=null;
var g_view=null;
function inMaintenance(displayMsg) {
if(!isset(displayMsg))
var displayMsg=true;
if(oPageProperties && oPageProperties.in_maintenance === '1') {
hideStatusMessage();
if(displayMsg)
frontendMessage({
'type': 'note',
'title': 'Maintenance',
'message': 'The current page is in maintenance mode.<br />Please be patient.'
}, 'maintenance');
return true;
} else {
return false;
}
}
function getHeaderHeight() {
if(g_header_height_cache === null) {
var ret=0;
var oHeader=document.getElementById('header');
if(oHeader) {
if(oHeader.style.display != 'none')
ret = oHeader.clientHeight;
}
g_header_height_cache = ret;
}
return g_header_height_cache;
}
function logout() {
call_ajax(oGeneralProperties.path_server+'?mod=Auth&act=logout', {
response_handler: function(response) {
if (response)
window.location.reload();
},
decode_json: false
});
}
function submitForm(sUrl, sFormId) {
var oResult=call_ajax(sUrl, {
method    : "POST",
post_data : getFormParams(sFormId, false),
response_handler : function(oResult) {
if (oResult && oResult.type) {
frontendMessage(oResult);
if (typeof popupWindowClose == 'function')
popupWindowClose();
} else {
popupWindowPutContent(oResult);
}
}
});
}
function updateForm(form) {
form._update.value = '1';
form._submit.click();
}
function clearFormValue(id) {
document.getElementById(id).value = '';
}
function showFrontendDialog(sUrl, sTitle, sWidth) {
if (typeof sWidth === 'undefined' || sWidth === null)
sWidth = 450;
call_ajax(sUrl, {
response_handler: function(response, data) {
if (isset(response)) {
response.url = sUrl;
if(typeof response !== 'undefined' && typeof response.code !== 'undefined') {
popupWindow(data.title, response, data.width);
}
}
},
handler_data: {
title: sTitle,
width: sWidth
}
});
}
function searchObjectsKeyCheck(sMatch, e) {
var charCode;
if(e && e.which) {
charCode = e.which;
} else if(window.event) {
e = window.event;
charCode = e.keyCode;
}
if(charCode == 13) {
searchObjects(sMatch);
}
}
function searchObjects(sMatch) {
var aResults=[];
var bMatch=false;
if (sMatch === '' || g_view === null)
return false;
var obj;
for(var i in g_view.objects) {
obj = g_view.objects[i];
if(obj.conf.type != 'shape'
&& obj.conf.type != 'textbox'
&& obj.conf.type != 'container'
&& obj.conf.type != 'line') {
bMatch = false;
var regex=new RegExp(sMatch, 'g');
if(obj.conf.type.search(regex) !== -1)
bMatch = true;
if(obj.conf.name.search(regex) !== -1)
bMatch = true;
if(obj.conf.type === 'service'
&& obj.conf.service_description.search(regex) !== -1)
bMatch = true;
regex = null;
if(bMatch === true)
aResults.push(i);
}
}
obj = null;
for(var i=0, len = aResults.length; i < len; i++) {
var objectId=aResults[i];
if(g_view.objects[objectId].conf.view_type && g_view.objects[objectId].conf.view_type === 'icon') {
setTimeout('flashIcon("'+objectId+'", '+oPageProperties.event_highlight_duration+', '+oPageProperties.event_highlight_interval+')', 0);
} else {
}
if(len == 1) {
setTimeout('scrollSlow('+g_view.objects[objectId].parsedX()+', '+g_view.objects[objectId].parsedY()+', 1)', 0);
}
objectId = null;
}
}
function getMapObjByDomObjId(id) {
try {
return g_view.objects[id];
} catch(er) {
return null;
}
}
function showAddModifyDialog(mapname, objectId) {
showFrontendDialog(oGeneralProperties.path_server
+ '?mod=Map&act=addModify&show='
+ escapeUrlValues(mapname)
+ '&object_id=' + escapeUrlValues(objectId), 'Modify Object');
}
function showAckDialog(map_name, objectId) {
showFrontendDialog(oGeneralProperties.path_server
+ '?mod=Action&act=acknowledge&map=' + escapeUrlValues(map_name)
+ '&object_id=' + escapeUrlValues(objectId), 'Acknowledge Problem');
}
function refreshMapObject(event, objectId, only_state) {
if (typeof only_state === 'undefined')
only_state = true;
var sMapPart='';
var sMod='';
var sAddPart='';
if (g_view.type === 'map') {
sMod = 'Map';
sMapPart = '&show='+escapeUrlValues(g_view.id);
sAddPart = getViewParams();
}
else if (g_view.type === 'overview') {
sMod = 'Overview';
sMapPart = '';
}
var ty=only_state ? 'state' : 'full';
call_ajax(oGeneralProperties.path_server+'?mod=' + sMod + '&act=getObjectStates'
+ sMapPart + '&ty='+ty+'&i[]=' + objectId + sAddPart, {
response_handler: function(response) {
g_view.updateObjects(response, only_state);
}
});
if (event)
return preventDefaultEvents(event);
}
function playSound(objectId, iNumTimes){
var sSound='';
var id=g_view.objects[objectId].dom_obj.id;
var oObjIcon=document.getElementById(id+'-icon');
var oObjIconDiv=document.getElementById(id+'-icondiv');
var sState=g_view.objects[objectId].conf.summary_state;
if(oStates[sState] && oStates[sState].sound && oStates[sState].sound !== '') {
sSound = oStates[sState].sound;
}
eventlog("state-change", "debug", "Sound to play: "+sSound);
if(sSound !== '') {
if(document.getElementById('sound'+sState)) {
document.body.removeChild(document.getElementById('sound'+sState));
}
var oEmbed=document.createElement('embed');
oEmbed.setAttribute('id', 'sound'+sState);
oEmbed.setAttribute('src', window.location.protocol + '//' + window.location.host + ':'
+ window.location.port + oGeneralProperties.path_sounds+sSound);
oEmbed.setAttribute('width', '0');
oEmbed.setAttribute('height', '0');
oEmbed.setAttribute('hidden', 'true');
oEmbed.setAttribute('loop', 'false');
oEmbed.setAttribute('autostart', 'true');
oEmbed.setAttribute('enablejavascript', 'true');
oEmbed = document.body.appendChild(oEmbed);
oEmbed = null;
iNumTimes = iNumTimes - 1;
if(iNumTimes > 0) {
setTimeout(function() { playSound(objectId, iNumTimes); }, 500);
}
}
oObjIcon = null;
oObjIconDiv = null;
}
function flashIcon(objectId, iDuration, iInterval){
if(isset(g_view.objects[objectId])) {
g_view.objects[objectId].highlight(!g_view.objects[objectId].bIsFlashing);
var iDurationNew=iDuration - iInterval;
if(iDurationNew > 0 || (iDurationNew <= 0 && g_view.objects[objectId].bIsFlashing === true))
setTimeout(function() { flashIcon(objectId, iDurationNew, iInterval); }, iInterval);
}
}
function set_fill_zoom_factor() {
var obj, zoom;
var c_top=null, c_left = null, c_bottom = null, c_right = null;
var o_top, o_left, o_bottom, o_right;
for(var i in g_view.objects) {
obj = g_view.objects[i];
if (obj && obj.getObjLeft && obj.getObjTop && obj.getObjHeight && obj.getObjWidth) {
o_top = obj.getObjTop();
if (c_top === null || o_top < c_top)
c_top = o_top;
o_left = obj.getObjLeft();
if (c_left === null || o_left < c_left)
c_left = o_left;
o_bottom = o_top + obj.getObjHeight();
if (c_bottom === null || o_bottom > c_bottom)
c_bottom = o_bottom;
o_right = o_left + obj.getObjWidth();
if (c_right === null || o_right > c_right)
c_right = o_right;
}
}
var border=40; // border per side in px * 2
var zoom_y=parseInt((pageHeight() - border - getHeaderHeight()) / parseFloat(c_bottom) * 100);
var zoom_x=parseInt((pageWidth() - border - getSidebarWidth())/ parseFloat(c_right) * 100);
set_zoom(Math.min(zoom_y, zoom_x));
}
function set_zoom(val) {
setViewParam('zoom', val);
if (g_worker_id)
window.clearTimeout(g_worker_id);
window.location = makeuri({'zoom': val});
}
function zoom(how) {
var cur_zoom=getZoomFactor();
if (cur_zoom == 'fill')
cur_zoom = 100;
var new_zoom=100;
if (how != 0) {
new_zoom = cur_zoom + how;
if (new_zoom <= 0 || new_zoom >= 200)
return;
}
if (cur_zoom != new_zoom) {
set_zoom(new_zoom);
}
}
function wheel_zoom(event) {
if (!event)
event = window.event;
var delta=0;
if (!event.altKey)
return; // only proceed with pressed ALT
if (event.wheelDelta) { // IE/Opera.
delta = event.wheelDelta/120;
} else if (event.detail) { // firefox
delta = -event.detail/3;
}
if (delta > 0) {
zoom(delta * 5);
} else if (delta < 0) {
zoom(delta * 5);
}
return preventDefaultEvents(event);
}
var g_drag_ind=null;
function zoombarDragStart(event) {
if (!event)
event = window.event;
if ((event.which === null && event.button >= 2) || (event.which !== null && event.which >= 2))
return; // skip clicks with other than left mouse
g_left_clicked = true;
g_drag_ind = document.getElementById('zoombar-drag_ind');
}
function zoombarDrag(event) {
if (!event)
event = window.event;
if (g_drag_ind === null)
return true;
if (!g_left_clicked) {
zoombarDragStop(event);
return;
}
var top_offset=62;
var ind_offset=3; // height / 2
var pos=(event.clientY - top_offset);
if (pos > g_drag_ind.parentNode.clientHeight) {
pos = g_drag_ind.parentNode.clientHeight;
} else if (pos < 0) {
pos = 0;
}
g_drag_ind.style.top = (pos - ind_offset) + 'px';
}
function zoombarDragStop(event) {
if (!event)
event = window.event;
if (g_drag_ind === null)
return true;
if ((event.which === null && event.button >= 2) || (event.which !== null && event.which >= 2))
return; // skip clicks with other than left mouse
g_left_clicked = false;
var zoom=getZoomFactor();
var val=parseInt((100 - (parseInt(g_drag_ind.style.top.replace('px', '')) + 3)) / 100 * 200);
if (val != zoom) {
if (val <= 0)
val = 10;
set_zoom(val);
}
g_drag_ind = null;
return preventDefaultEvents(event);
}
var g_left_clicked=false;
function mouse_click(event) {
if (!event)
event = window.event;
if ((event.which === null && event.button >= 2) || (event.which !== null && event.which >= 2))
return; // skip clicks with other than left mouse
g_left_clicked = true;
}
function mouse_release(event) {
if (!event)
event = window.event;
if ((event.which === null && event.button >= 2) || (event.which !== null && event.which >= 2))
return; // skip clicks with other than left mouse
g_left_clicked = false;
zoombarDragStop(event);
}
function updateZoomIndicator() {
var zoom=getZoomFactor();
var ind=document.getElementById('zoombar-drag_ind');
ind.style.top = (100 - ((zoom / 200 * 100)) - 3) + 'px';
ind = null;
}
function renderZoombar() {
if (getViewParam('zoombar') == 0)
return;
var bar=document.createElement('div');
bar.setAttribute('id', 'zoombar');
var plus=document.createElement('a');
plus.setAttribute('id', 'zoombar-plus');
plus.setAttribute('class', 'plus');
plus.appendChild(document.createTextNode('+'));
plus.onclick = function() {
zoom(10);
};
bar.appendChild(plus);
var drag=document.createElement('div');
drag.setAttribute('id', 'zoombar-drag');
drag.setAttribute('class', 'drag');
bar.appendChild(drag);
var drag_ind=document.createElement('div');
drag_ind.setAttribute('id', 'zoombar-drag_ind');
drag_ind.setAttribute('class', 'drag_ind');
addEvent(drag_ind, 'mousedown', zoombarDragStart);
addEvent(drag,     'mousemove', zoombarDrag);
addEvent(drag,     'mouseup',   zoombarDragStop);
drag.appendChild(drag_ind);
var minus=document.createElement('a');
minus.setAttribute('id', 'zoombar-minus');
minus.setAttribute('class', 'minus');
minus.appendChild(document.createTextNode('-'));
minus.onclick = function() {
zoom(-10);
};
bar.appendChild(minus);
var norm=document.createElement('a');
norm.setAttribute('class', 'norm');
norm.appendChild(document.createTextNode('o'));
norm.onclick = function() {
zoom(0);
};
bar.appendChild(norm);
var wheel_event=(/Firefox/i.test(navigator.userAgent)) ? "DOMMouseScroll" : "mousewheel";
addEvent(document, wheel_event, wheel_zoom);
addEvent(document, 'mousedown', mouse_click);
addEvent(document, 'mouseup',   mouse_release);
document.body.appendChild(bar);
updateZoomIndicator();
}
function getViewParams(update, userParams) {
if(!isset(userParams))
userParams = false;
if(!userParams && isset(oViewProperties) && isset(oViewProperties['params'])) {
var params=oViewProperties['params'];
} else if(isset(oViewProperties) && isset(oViewProperties['user_params'])) {
var params=oViewProperties['user_params'];
} else if(update) {
var params={}
} else {
return '';
}
if(isset(update)) {
for(var param in update) {
params[param] = update[param];
}
}
if(!isset(params))
return '';
if (g_map && usesSource('worldmap'))
params['bbox'] = g_map.getBounds().toBBoxString();
var sParams='';
for(var param in params) {
if(params[param] != '') {
sParams += '&' + param + '=' + escapeUrlValues(params[param]);
}
}
return sParams;
}
function getViewParam(param) {
if (oViewProperties && isset(oViewProperties['params'])
&& isset(oViewProperties['params'][param]))
return oViewProperties['params'][param];
return null;
}
function setViewParam(param, val) {
oViewProperties['params'][param] = val;
oViewProperties['user_params'][param] = val;
}
function usesSource(source) {
return oPageProperties
&& oPageProperties.sources
&& oPageProperties.sources.indexOf(source) !== -1;
}
function hasNeededJSFeatures() {
var msg=null;
if (typeof JSON === 'undefined') {
msg = 'It seems you are using an outdated browser to access NagVis. '
+'I am sorry, but you will not be able to use NagVis with this '
+'old browser. Please consider updating. (Missing JSON)';
}
if (msg) {
frontendMessage({
'type'     : 'error',
'title'    : 'Error: Outdated Browser',
'message'  : msg,
'closable' : false
});
return false;
} else {
return true;
}
}
function workerInitialize(type, ident) {
displayStatusMessage('Loading...', 'loading', true);
switch (type) {
case 'map':
if (usesSource('worldmap'))
g_view = new ViewWorldmap(ident);
else
g_view = new ViewMap(ident);
break;
case 'overview':
g_view = new ViewOverview();
break;
case 'url':
g_view = new ViewUrl(ident);
break;
default:
eventlog("worker", "error", "Unknown view type: "+type);
hideStatusMessage();
return;
}
g_view.init();
}
function workerUpdate(iCount, sType, sIdentifier) {
eventlog("worker", "debug", "Update (Run-ID: "+iCount+")");
oWorkerProperties.last_run = iNow;
g_view.update();
updateWorkerCounter(); // Update the worker last run time on maps
}
function runWorker(iCount, sType, sIdentifier) {
if(iCount === 0) {
if (!hasNeededJSFeatures())
return; // sorry!
workerInitialize(sType, sIdentifier);
} else {
iNow = Math.floor(Date.parse(new Date()) / 1000);
if(rotationCountdown() === true) {
eventlog("worker", "debug", "Worker stopped: Rotate/Refresh detected");
return false;
}
if(iCount % oWorkerProperties.worker_interval === 0)
workerUpdate(iCount, sType, sIdentifier);
}
g_worker_id = window.setTimeout(function() {
runWorker((iCount+1), sType, sIdentifier);
}, 1000);
}
var jg_ok, jg_ie, jg_fast, jg_dom, jg_moz;
function _chkDHTM(wnd, x, i)
{
x = wnd.document.body || null;
jg_ie = x && typeof x.insertAdjacentHTML != "undefined" && wnd.document.createElement;
jg_dom = (x && !jg_ie &&
typeof x.appendChild != "undefined" &&
typeof wnd.document.createRange != "undefined" &&
typeof (i = wnd.document.createRange()).setStartBefore != "undefined" &&
typeof i.createContextualFragment != "undefined");
jg_fast = jg_ie && wnd.document.all && !wnd.opera;
jg_moz = jg_dom && typeof x.style.MozOpacity != "undefined";
jg_ok = !!(jg_ie || jg_dom);
}
function _pntCnvDom()
{
var x=this.wnd.document.createRange();
x.setStartBefore(this.cnv);
x = x.createContextualFragment(jg_fast? this._htmRpc() : this.htm);
if(this.cnv) this.cnv.appendChild(x);
this.htm = "";
}
function _pntCnvIe()
{
if(this.cnv) this.cnv.insertAdjacentHTML("BeforeEnd", jg_fast? this._htmRpc() : this.htm);
this.htm = "";
}
function _pntDoc()
{
this.wnd.document.write(jg_fast? this._htmRpc() : this.htm);
this.htm = '';
}
function _pntN() {
}
function _mkDiv(x, y, w, h)
{
this.htm += '<div style="position:absolute;'+
'left:' + x + 'px;'+
'top:' + y + 'px;'+
'width:' + w + 'px;'+
'height:' + h + 'px;'+
'clip:rect(0,'+w+'px,'+h+'px,0);'+
'background-color:' + this.color +
(!jg_moz? ';overflow:hidden' : '')+
';"><\/div>';
}
function _mkDivIe(x, y, w, h)
{
this.htm += '%%'+this.color+';'+x+';'+y+';'+w+';'+h+';';
}
function _mkDivPrt(x, y, w, h)
{
this.htm += '<div style="position:absolute;'+
'border-left:' + w + 'px solid ' + this.color + ';'+
'left:' + x + 'px;'+
'top:' + y + 'px;'+
'width:0px;'+
'height:' + h + 'px;'+
'clip:rect(0,'+w+'px,'+h+'px,0);'+
'background-color:' + this.color +
(!jg_moz? ';overflow:hidden' : '')+
';"><\/div>';
}
var _regex=/%%([^;]+);([^;]+);([^;]+);([^;]+);([^;]+);/g;
function _htmRpc()
{
return this.htm.replace(
_regex,
'<div style="overflow:hidden;position:absolute;background-color:'+
'$1;left:$2px;top:$3px;width:$4px;height:$5px"></div>\n');
}
function _htmPrtRpc()
{
return this.htm.replace(
_regex,
'<div style="overflow:hidden;position:absolute;background-color:'+
'$1;left:$2px;top:$3px;width:$4px;height:$5px;border-left:$4px solid $1"></div>\n');
}
function _mkLin(x1, y1, x2, y2)
{
if(x1 > x2)
{
var _x2=x2;
var _y2=y2;
x2 = x1;
y2 = y1;
x1 = _x2;
y1 = _y2;
}
var dx=x2-x1, dy = Math.abs(y2-y1),
x = x1, y = y1,
yIncr = (y1 > y2)? -1 : 1;
if(dx >= dy)
{
var pr=dy<<1,
pru = pr - (dx<<1),
p = pr-dx,
ox = x;
while(dx > 0)
{--dx;
++x;
if(p > 0)
{
this._mkDiv(ox, y, x-ox, 1);
y += yIncr;
p += pru;
ox = x;
}
else p += pr;
}
this._mkDiv(ox, y, x2-ox+1, 1);
}
else
{
var pr=dx<<1,
pru = pr - (dy<<1),
p = pr-dy,
oy = y;
if(y2 <= y1)
{
while(dy > 0)
{--dy;
if(p > 0)
{
this._mkDiv(x++, y, 1, oy-y+1);
y += yIncr;
p += pru;
oy = y;
}
else
{
y += yIncr;
p += pr;
}
}
this._mkDiv(x2, y2, 1, oy-y2+1);
}
else
{
while(dy > 0)
{--dy;
y += yIncr;
if(p > 0)
{
this._mkDiv(x++, oy, 1, y-oy);
p += pru;
oy = y;
}
else p += pr;
}
this._mkDiv(x2, oy, 1, y2-oy+1);
}
}
}
function _mkLin2D(x1, y1, x2, y2)
{
if(x1 > x2)
{
var _x2=x2;
var _y2=y2;
x2 = x1;
y2 = y1;
x1 = _x2;
y1 = _y2;
}
var dx=x2-x1, dy = Math.abs(y2-y1),
x = x1, y = y1,
yIncr = (y1 > y2)? -1 : 1;
var s=this.stroke;
if(dx >= dy)
{
if(dx > 0 && s-3 > 0)
{
var _s=(s*dx*Math.sqrt(1+dy*dy/(dx*dx))-dx-(s>>1)*dy) / dx;
_s = (!(s-4)? Math.ceil(_s) : Math.round(_s)) + 1;
}
else var _s=s;
var ad=Math.ceil(s/2);
var pr=dy<<1,
pru = pr - (dx<<1),
p = pr-dx,
ox = x;
while(dx > 0)
{--dx;
++x;
if(p > 0)
{
this._mkDiv(ox, y, x-ox+ad, _s);
y += yIncr;
p += pru;
ox = x;
}
else p += pr;
}
this._mkDiv(ox, y, x2-ox+ad+1, _s);
}
else
{
if(s-3 > 0)
{
var _s=(s*dy*Math.sqrt(1+dx*dx/(dy*dy))-(s>>1)*dx-dy) / dy;
_s = (!(s-4)? Math.ceil(_s) : Math.round(_s)) + 1;
}
else var _s=s;
var ad=Math.round(s/2);
var pr=dx<<1,
pru = pr - (dy<<1),
p = pr-dy,
oy = y;
if(y2 <= y1)
{
++ad;
while(dy > 0)
{--dy;
if(p > 0)
{
this._mkDiv(x++, y, _s, oy-y+ad);
y += yIncr;
p += pru;
oy = y;
}
else
{
y += yIncr;
p += pr;
}
}
this._mkDiv(x2, y2, _s, oy-y2+ad);
}
else
{
while(dy > 0)
{--dy;
y += yIncr;
if(p > 0)
{
this._mkDiv(x++, oy, _s, y-oy+ad);
p += pru;
oy = y;
}
else p += pr;
}
this._mkDiv(x2, oy, _s, y2-oy+ad+1);
}
}
}
function _mkLinDott(x1, y1, x2, y2)
{
if(x1 > x2)
{
var _x2=x2;
var _y2=y2;
x2 = x1;
y2 = y1;
x1 = _x2;
y1 = _y2;
}
var dx=x2-x1, dy = Math.abs(y2-y1),
x = x1, y = y1,
yIncr = (y1 > y2)? -1 : 1,
drw = true;
if(dx >= dy)
{
var pr=dy<<1,
pru = pr - (dx<<1),
p = pr-dx;
while(dx > 0)
{--dx;
if(drw) this._mkDiv(x, y, 1, 1);
drw = !drw;
if(p > 0)
{
y += yIncr;
p += pru;
}
else p += pr;
++x;
}
}
else
{
var pr=dx<<1,
pru = pr - (dy<<1),
p = pr-dy;
while(dy > 0)
{--dy;
if(drw) this._mkDiv(x, y, 1, 1);
drw = !drw;
y += yIncr;
if(p > 0)
{
++x;
p += pru;
}
else p += pr;
}
}
if(drw) this._mkDiv(x, y, 1, 1);
}
function _mkOv(left, top, width, height)
{
var a=(++width)>>1, b = (++height)>>1,
wod = width&1, hod = height&1,
cx = left+a, cy = top+b,
x = 0, y = b,
ox = 0, oy = b,
aa2 = (a*a)<<1, aa4 = aa2<<1, bb2 = (b*b)<<1, bb4 = bb2<<1,
st = (aa2>>1)*(1-(b<<1)) + bb2,
tt = (bb2>>1) - aa2*((b<<1)-1),
w, h;
while(y > 0)
{
if(st < 0)
{
st += bb2*((x<<1)+3);
tt += bb4*(++x);
}
else if(tt < 0)
{
st += bb2*((x<<1)+3) - aa4*(y-1);
tt += bb4*(++x) - aa2*(((y--)<<1)-3);
w = x-ox;
h = oy-y;
if((w&2) && (h&2))
{
this._mkOvQds(cx, cy, x-2, y+2, 1, 1, wod, hod);
this._mkOvQds(cx, cy, x-1, y+1, 1, 1, wod, hod);
}
else this._mkOvQds(cx, cy, x-1, oy, w, h, wod, hod);
ox = x;
oy = y;
}
else
{
tt -= aa2*((y<<1)-3);
st -= aa4*(--y);
}
}
w = a-ox+1;
h = (oy<<1)+hod;
y = cy-oy;
this._mkDiv(cx-a, y, w, h);
this._mkDiv(cx+ox+wod-1, y, w, h);
}
function _mkOv2D(left, top, width, height)
{
var s=this.stroke;
width += s+1;
height += s+1;
var a=width>>1, b = height>>1,
wod = width&1, hod = height&1,
cx = left+a, cy = top+b,
x = 0, y = b,
aa2 = (a*a)<<1, aa4 = aa2<<1, bb2 = (b*b)<<1, bb4 = bb2<<1,
st = (aa2>>1)*(1-(b<<1)) + bb2,
tt = (bb2>>1) - aa2*((b<<1)-1);
if(s-4 < 0 && (!(s-2) || width-51 > 0 && height-51 > 0))
{
var ox=0, oy = b,
w, h,
pxw;
while(y > 0)
{
if(st < 0)
{
st += bb2*((x<<1)+3);
tt += bb4*(++x);
}
else if(tt < 0)
{
st += bb2*((x<<1)+3) - aa4*(y-1);
tt += bb4*(++x) - aa2*(((y--)<<1)-3);
w = x-ox;
h = oy-y;
if(w-1)
{
pxw = w+1+(s&1);
h = s;
}
else if(h-1)
{
pxw = s;
h += 1+(s&1);
}
else pxw = h = s;
this._mkOvQds(cx, cy, x-1, oy, pxw, h, wod, hod);
ox = x;
oy = y;
}
else
{
tt -= aa2*((y<<1)-3);
st -= aa4*(--y);
}
}
this._mkDiv(cx-a, cy-oy, s, (oy<<1)+hod);
this._mkDiv(cx+a+wod-s, cy-oy, s, (oy<<1)+hod);
}
else
{
var _a=(width-(s<<1))>>1,
_b = (height-(s<<1))>>1,
_x = 0, _y = _b,
_aa2 = (_a*_a)<<1, _aa4 = _aa2<<1, _bb2 = (_b*_b)<<1, _bb4 = _bb2<<1,
_st = (_aa2>>1)*(1-(_b<<1)) + _bb2,
_tt = (_bb2>>1) - _aa2*((_b<<1)-1),
pxl = new Array(),
pxt = new Array(),
_pxb = new Array();
pxl[0] = 0;
pxt[0] = b;
_pxb[0] = _b-1;
while(y > 0)
{
if(st < 0)
{
pxl[pxl.length] = x;
pxt[pxt.length] = y;
st += bb2*((x<<1)+3);
tt += bb4*(++x);
}
else if(tt < 0)
{
pxl[pxl.length] = x;
st += bb2*((x<<1)+3) - aa4*(y-1);
tt += bb4*(++x) - aa2*(((y--)<<1)-3);
pxt[pxt.length] = y;
}
else
{
tt -= aa2*((y<<1)-3);
st -= aa4*(--y);
}
if(_y > 0)
{
if(_st < 0)
{
_st += _bb2*((_x<<1)+3);
_tt += _bb4*(++_x);
_pxb[_pxb.length] = _y-1;
}
else if(_tt < 0)
{
_st += _bb2*((_x<<1)+3) - _aa4*(_y-1);
_tt += _bb4*(++_x) - _aa2*(((_y--)<<1)-3);
_pxb[_pxb.length] = _y-1;
}
else
{
_tt -= _aa2*((_y<<1)-3);
_st -= _aa4*(--_y);
_pxb[_pxb.length-1]--;
}
}
}
var ox=-wod, oy = b,
_oy = _pxb[0],
l = pxl.length,
w, h;
for(var i=0; i < l; i++)
{
if(typeof _pxb[i] != "undefined")
{
if(_pxb[i] < _oy || pxt[i] < oy)
{
x = pxl[i];
this._mkOvQds(cx, cy, x, oy, x-ox, oy-_oy, wod, hod);
ox = x;
oy = pxt[i];
_oy = _pxb[i];
}
}
else
{
x = pxl[i];
this._mkDiv(cx-x, cy-oy, 1, (oy<<1)+hod);
this._mkDiv(cx+ox+wod, cy-oy, 1, (oy<<1)+hod);
ox = x;
oy = pxt[i];
}
}
this._mkDiv(cx-a, cy-oy, 1, (oy<<1)+hod);
this._mkDiv(cx+ox+wod, cy-oy, 1, (oy<<1)+hod);
}
}
function _mkOvDott(left, top, width, height)
{
var a=(++width)>>1, b = (++height)>>1,
wod = width&1, hod = height&1, hodu = hod^1,
cx = left+a, cy = top+b,
x = 0, y = b,
aa2 = (a*a)<<1, aa4 = aa2<<1, bb2 = (b*b)<<1, bb4 = bb2<<1,
st = (aa2>>1)*(1-(b<<1)) + bb2,
tt = (bb2>>1) - aa2*((b<<1)-1),
drw = true;
while(y > 0)
{
if(st < 0)
{
st += bb2*((x<<1)+3);
tt += bb4*(++x);
}
else if(tt < 0)
{
st += bb2*((x<<1)+3) - aa4*(y-1);
tt += bb4*(++x) - aa2*(((y--)<<1)-3);
}
else
{
tt -= aa2*((y<<1)-3);
st -= aa4*(--y);
}
if(drw && y >= hodu) this._mkOvQds(cx, cy, x, y, 1, 1, wod, hod);
drw = !drw;
}
}
function _mkRect(x, y, w, h)
{
var s=this.stroke;
this._mkDiv(x, y, w, s);
this._mkDiv(x+w, y, s, h);
this._mkDiv(x, y+h, w+s, s);
this._mkDiv(x, y+s, s, h-s);
}
function _mkRectDott(x, y, w, h)
{
this.drawLine(x, y, x+w, y);
this.drawLine(x+w, y, x+w, y+h);
this.drawLine(x, y+h, x+w, y+h);
this.drawLine(x, y, x, y+h);
}
function jsgFont()
{
this.PLAIN = 'font-weight:normal;';
this.BOLD = 'font-weight:bold;';
this.ITALIC = 'font-style:italic;';
this.ITALIC_BOLD = this.ITALIC + this.BOLD;
this.BOLD_ITALIC = this.ITALIC_BOLD;
}
var Font=new jsgFont();
function jsgStroke()
{
this.DOTTED = -1;
}
var Stroke=new jsgStroke();
function jsGraphics(cnv, wnd)
{
this.setColor = function(x)
{
this.color = x.toLowerCase();
};
this.setStroke = function(x)
{
this.stroke = x;
if(!(x+1))
{
this.drawLine = _mkLinDott;
this._mkOv = _mkOvDott;
this.drawRect = _mkRectDott;
}
else if(x-1 > 0)
{
this.drawLine = _mkLin2D;
this._mkOv = _mkOv2D;
this.drawRect = _mkRect;
}
else
{
this.drawLine = _mkLin;
this._mkOv = _mkOv;
this.drawRect = _mkRect;
}
};
this.setPrintable = function(arg)
{
this.printable = arg;
if(jg_fast)
{
this._mkDiv = _mkDivIe;
this._htmRpc = arg? _htmPrtRpc : _htmRpc;
}
else this._mkDiv = arg? _mkDivPrt : _mkDiv;
};
this.setFont = function(fam, sz, sty)
{
this.ftFam = fam;
this.ftSz = sz;
this.ftSty = sty || Font.PLAIN;
};
this.drawPolyline = this.drawPolyLine = function(x, y)
{
for (var i=x.length - 1; i;)
{--i;
this.drawLine(x[i], y[i], x[i+1], y[i+1]);
}
};
this.fillRect = function(x, y, w, h)
{
this._mkDiv(x, y, w, h);
};
this.drawPolygon = function(x, y)
{
this.drawPolyline(x, y);
this.drawLine(x[x.length-1], y[x.length-1], x[0], y[0]);
};
this.drawEllipse = this.drawOval = function(x, y, w, h)
{
this._mkOv(x, y, w, h);
};
this.fillEllipse = this.fillOval = function(left, top, w, h)
{
var a=w>>1, b = h>>1,
wod = w&1, hod = h&1,
cx = left+a, cy = top+b,
x = 0, y = b, oy = b,
aa2 = (a*a)<<1, aa4 = aa2<<1, bb2 = (b*b)<<1, bb4 = bb2<<1,
st = (aa2>>1)*(1-(b<<1)) + bb2,
tt = (bb2>>1) - aa2*((b<<1)-1),
xl, dw, dh;
if(w) while(y > 0)
{
if(st < 0)
{
st += bb2*((x<<1)+3);
tt += bb4*(++x);
}
else if(tt < 0)
{
st += bb2*((x<<1)+3) - aa4*(y-1);
xl = cx-x;
dw = (x<<1)+wod;
tt += bb4*(++x) - aa2*(((y--)<<1)-3);
dh = oy-y;
this._mkDiv(xl, cy-oy, dw, dh);
this._mkDiv(xl, cy+y+hod, dw, dh);
oy = y;
}
else
{
tt -= aa2*((y<<1)-3);
st -= aa4*(--y);
}
}
this._mkDiv(cx-a, cy-oy, w, (oy<<1)+hod);
};
this.fillArc = function(iL, iT, iW, iH, fAngA, fAngZ)
{
var a=iW>>1, b = iH>>1,
iOdds = (iW&1) | ((iH&1) << 16),
cx = iL+a, cy = iT+b,
x = 0, y = b, ox = x, oy = y,
aa2 = (a*a)<<1, aa4 = aa2<<1, bb2 = (b*b)<<1, bb4 = bb2<<1,
st = (aa2>>1)*(1-(b<<1)) + bb2,
tt = (bb2>>1) - aa2*((b<<1)-1),
xEndA, yEndA, xEndZ, yEndZ,
iSects = (1 << (Math.floor((fAngA %= 360.0)/180.0) << 3))
| (2 << (Math.floor((fAngZ %= 360.0)/180.0) << 3))
| ((fAngA >= fAngZ) << 16),
aBndA = new Array(b+1), aBndZ = new Array(b+1);
fAngA *= Math.PI/180.0;
fAngZ *= Math.PI/180.0;
xEndA = cx+Math.round(a*Math.cos(fAngA));
yEndA = cy+Math.round(-b*Math.sin(fAngA));
_mkLinVirt(aBndA, cx, cy, xEndA, yEndA);
xEndZ = cx+Math.round(a*Math.cos(fAngZ));
yEndZ = cy+Math.round(-b*Math.sin(fAngZ));
_mkLinVirt(aBndZ, cx, cy, xEndZ, yEndZ);
while(y > 0)
{
if(st < 0) // Advance x
{
st += bb2*((x<<1)+3);
tt += bb4*(++x);
}
else if(tt < 0) // Advance x and y
{
st += bb2*((x<<1)+3) - aa4*(y-1);
ox = x;
tt += bb4*(++x) - aa2*(((y--)<<1)-3);
this._mkArcDiv(ox, y, oy, cx, cy, iOdds, aBndA, aBndZ, iSects);
oy = y;
}
else // Advance y
{
tt -= aa2*((y<<1)-3);
st -= aa4*(--y);
if(y && (aBndA[y] != aBndA[y-1] || aBndZ[y] != aBndZ[y-1]))
{
this._mkArcDiv(x, y, oy, cx, cy, iOdds, aBndA, aBndZ, iSects);
ox = x;
oy = y;
}
}
}
this._mkArcDiv(x, 0, oy, cx, cy, iOdds, aBndA, aBndZ, iSects);
if(iOdds >> 16) // Odd height
{
if(iSects >> 16) // Start-angle > end-angle
{
var xl=(yEndA <= cy || yEndZ > cy)? (cx - x) : cx;
this._mkDiv(xl, cy, x + cx - xl + (iOdds & 0xffff), 1);
}
else if((iSects & 0x01) && yEndZ > cy)
this._mkDiv(cx - x, cy, x, 1);
}
};
this.fillPolygon = function(array_x, array_y)
{
var i;
var y;
var miny, maxy;
var x1, y1;
var x2, y2;
var ind1, ind2;
var ints;
var n=array_x.length;
if(!n) return;
miny = array_y[0];
maxy = array_y[0];
for(i = 1; i < n; i++)
{
if(array_y[i] < miny)
miny = array_y[i];
if(array_y[i] > maxy)
maxy = array_y[i];
}
for(y = miny; y <= maxy; y++)
{
var polyInts=new Array();
ints = 0;
for(i = 0; i < n; i++)
{
if(!i)
{
ind1 = n-1;
ind2 = 0;
}
else
{
ind1 = i-1;
ind2 = i;
}
y1 = array_y[ind1];
y2 = array_y[ind2];
if(y1 < y2)
{
x1 = array_x[ind1];
x2 = array_x[ind2];
}
else if(y1 > y2)
{
y2 = array_y[ind1];
y1 = array_y[ind2];
x2 = array_x[ind1];
x1 = array_x[ind2];
}
else continue;
if((y >= y1) && (y < y2))
polyInts[ints++] = Math.round((y-y1) * (x2-x1) / (y2-y1) + x1);
else if((y == maxy) && (y > y1) && (y <= y2))
polyInts[ints++] = Math.round((y-y1) * (x2-x1) / (y2-y1) + x1);
}
polyInts.sort(_CompInt);
for(i = 0; i < ints; i+=2)
this._mkDiv(polyInts[i], y, polyInts[i+1]-polyInts[i]+1, 1);
}
};
this.drawString = function(txt, x, y)
{
this.htm += '<div style="position:absolute;white-space:nowrap;'+
'left:' + x + 'px;'+
'top:' + y + 'px;'+
'font-family:' +  this.ftFam + ';'+
'font-size:' + this.ftSz + ';'+
'color:' + this.color + ';' + this.ftSty + '">'+
txt +
'<\/div>';
};
this.drawStringRect = function(txt, x, y, width, halign)
{
this.htm += '<div style="position:absolute;overflow:hidden;'+
'left:' + x + 'px;'+
'top:' + y + 'px;'+
'width:'+width +'px;'+
'text-align:'+halign+';'+
'font-family:' +  this.ftFam + ';'+
'font-size:' + this.ftSz + ';'+
'color:' + this.color + ';' + this.ftSty + '">'+
txt +
'<\/div>';
};
this.drawImage = function(imgSrc, x, y, w, h, a)
{
this.htm += '<div style="position:absolute;'+
'left:' + x + 'px;'+
'top:' + y + 'px;'+
(w? ('width:' +  w + 'px;') : '') +
(h? ('height:' + h + 'px;'):'')+'">'+
'<img src="' + imgSrc +'"'+ (w ? (' width="' + w + '"'):'')+ (h ? (' height="' + h + '"'):'') + (a? (' '+a) : '') + '>'+
'<\/div>';
};
this.clear = function()
{
this.htm = "";
if(this.cnv) this.cnv.innerHTML = "";
};
this._mkOvQds = function(cx, cy, x, y, w, h, wod, hod)
{
var xl=cx - x, xr = cx + x + wod - w, yt = cy - y, yb = cy + y + hod - h;
if(xr > xl+w)
{
this._mkDiv(xr, yt, w, h);
this._mkDiv(xr, yb, w, h);
}
else
w = xr - xl + w;
this._mkDiv(xl, yt, w, h);
this._mkDiv(xl, yb, w, h);
};
this._mkArcDiv = function(x, y, oy, cx, cy, iOdds, aBndA, aBndZ, iSects)
{
var xrDef=cx + x + (iOdds & 0xffff), y2, h = oy - y, xl, xr, w;
if(!h) h = 1;
x = cx - x;
if(iSects & 0xff0000) // Start-angle > end-angle
{
y2 = cy - y - h;
if(iSects & 0x00ff)
{
if(iSects & 0x02)
{
xl = Math.max(x, aBndZ[y]);
w = xrDef - xl;
if(w > 0) this._mkDiv(xl, y2, w, h);
}
if(iSects & 0x01)
{
xr = Math.min(xrDef, aBndA[y]);
w = xr - x;
if(w > 0) this._mkDiv(x, y2, w, h);
}
}
else
this._mkDiv(x, y2, xrDef - x, h);
y2 = cy + y + (iOdds >> 16);
if(iSects & 0xff00)
{
if(iSects & 0x0100)
{
xl = Math.max(x, aBndA[y]);
w = xrDef - xl;
if(w > 0) this._mkDiv(xl, y2, w, h);
}
if(iSects & 0x0200)
{
xr = Math.min(xrDef, aBndZ[y]);
w = xr - x;
if(w > 0) this._mkDiv(x, y2, w, h);
}
}
else
this._mkDiv(x, y2, xrDef - x, h);
}
else
{
if(iSects & 0x00ff)
{
if(iSects & 0x02)
xl = Math.max(x, aBndZ[y]);
else
xl = x;
if(iSects & 0x01)
xr = Math.min(xrDef, aBndA[y]);
else
xr = xrDef;
y2 = cy - y - h;
w = xr - xl;
if(w > 0) this._mkDiv(xl, y2, w, h);
}
if(iSects & 0xff00)
{
if(iSects & 0x0100)
xl = Math.max(x, aBndA[y]);
else
xl = x;
if(iSects & 0x0200)
xr = Math.min(xrDef, aBndZ[y]);
else
xr = xrDef;
y2 = cy + y + (iOdds >> 16);
w = xr - xl;
if(w > 0) this._mkDiv(xl, y2, w, h);
}
}
};
this.setStroke(1);
this.setFont("verdana,geneva,helvetica,sans-serif", "12px", Font.PLAIN);
this.color = "#000000";
this.htm = "";
this.wnd = wnd || window;
if(!jg_ok) _chkDHTM(this.wnd);
if(jg_ok)
{
if(cnv)
{
if(typeof(cnv) == "string")
this.cont = document.all? (this.wnd.document.all[cnv] || null)
: document.getElementById? (this.wnd.document.getElementById(cnv) || null)
: null;
else if(cnv == window.document)
this.cont = document.getElementsByTagName("body")[0];
else this.cont = cnv;
this.cnv = this.wnd.document.createElement("div");
this.cnv.style.fontSize=0;
this.cont.appendChild(this.cnv);
this.paint = jg_dom? _pntCnvDom : _pntCnvIe;
}
else
this.paint = _pntDoc;
}
else
this.paint = _pntN;
this.setPrintable(false);
}
function _mkLinVirt(aLin, x1, y1, x2, y2)
{
var dx=Math.abs(x2-x1), dy = Math.abs(y2-y1),
x = x1, y = y1,
xIncr = (x1 > x2)? -1 : 1,
yIncr = (y1 > y2)? -1 : 1,
p,
i = 0;
if(dx >= dy)
{
var pr=dy<<1,
pru = pr - (dx<<1);
p = pr-dx;
while(dx > 0)
{--dx;
if(p > 0)    //  Increment y
{
aLin[i++] = x;
y += yIncr;
p += pru;
}
else p += pr;
x += xIncr;
}
}
else
{
var pr=dx<<1,
pru = pr - (dy<<1);
p = pr-dy;
while(dy > 0)
{--dy;
y += yIncr;
aLin[i++] = x;
if(p > 0)    //  Increment x
{
x += xIncr;
p += pru;
}
else p += pr;
}
}
for(var len=aLin.length, i = len-i; i;)
aLin[len-(i--)] = x;
};
function _CompInt(x, y)
{
return(x - y);
}
var jscolor={
dir : '', // location of jscolor directory (leave empty to autodetect)
bindClass : 'color', // class name
binding : false, // automatic binding via <input class="...">
preloading : true, // use image preloading?
install : function() {
jscolor.addEvent(window, 'load', jscolor.init);
},
init : function() {
if(jscolor.binding) {
jscolor.bind();
}
if(jscolor.preloading) {
jscolor.preload();
}
},
getDir : function() {
if(!jscolor.dir) {
var detected=jscolor.detectDir();
jscolor.dir = detected!==false ? detected : 'jscolor/';
}
return jscolor.dir;
},
detectDir : function() {
var base=location.href;
var e=document.getElementsByTagName('base');
for(var i=0; i<e.length; i+=1) {
if(e[i].href) { base = e[i].href; }
}
var e=document.getElementsByTagName('script');
for(var i=0; i<e.length; i+=1) {
if(e[i].src && /(^|\/)jscolor\.js([?#].*)?$/i.test(e[i].src)) {
var src=new jscolor.URI(e[i].src);
var srcAbs=src.toAbsolute(base);
srcAbs.path = srcAbs.path.replace(/[^\/]+$/, ''); // remove filename
srcAbs.query = null;
srcAbs.fragment = null;
return srcAbs.toString();
}
}
return false;
},
bind : function() {
var matchClass=new RegExp('(^|\\s)('+jscolor.bindClass+')\\s*(\\{[^}]*\\})?', 'i');
var e=document.getElementsByTagName('input');
for(var i=0; i<e.length; i+=1) {
var m;
if(!e[i].color && e[i].className && (m = e[i].className.match(matchClass))) {
var prop={};
if(m[3]) {
try {
eval('prop='+m[3]);
} catch(eInvalidProp) {}
}
e[i].color = new jscolor.color(e[i], prop);
}
}
},
preload : function() {
for(var fn in jscolor.imgRequire) {
if(jscolor.imgRequire.hasOwnProperty(fn)) {
jscolor.loadImage(fn);
}
}
},
images : {
pad : [ 181, 101 ],
sld : [ 16, 101 ],
cross : [ 15, 15 ],
arrow : [ 7, 11 ]
},
imgRequire : {},
imgLoaded : {},
requireImage : function(filename) {
jscolor.imgRequire[filename] = true;
},
loadImage : function(filename) {
if(!jscolor.imgLoaded[filename]) {
jscolor.imgLoaded[filename] = new Image();
jscolor.imgLoaded[filename].src = jscolor.getDir()+filename;
}
},
fetchElement : function(mixed) {
return typeof mixed === 'string' ? document.getElementById(mixed) : mixed;
},
addEvent : function(el, evnt, func) {
if(el.addEventListener) {
el.addEventListener(evnt, func, false);
} else if(el.attachEvent) {
el.attachEvent('on'+evnt, func);
}
},
fireEvent : function(el, evnt) {
if(!el) {
return;
}
if(document.createEvent) {
var ev=document.createEvent('HTMLEvents');
ev.initEvent(evnt, true, true);
el.dispatchEvent(ev);
} else if(document.createEventObject) {
var ev=document.createEventObject();
el.fireEvent('on'+evnt, ev);
} else if(el['on'+evnt]) { // alternatively use the traditional event model (IE5)
el['on'+evnt]();
}
},
getElementPos : function(e) {
var e1=e, e2=e;
var x=0, y=0;
if(e1.offsetParent) {
do {
x += e1.offsetLeft;
y += e1.offsetTop;
} while(e1 = e1.offsetParent);
}
while((e2 = e2.parentNode) && e2.nodeName.toUpperCase() !== 'BODY') {
x -= e2.scrollLeft;
y -= e2.scrollTop;
}
return [x, y];
},
getElementSize : function(e) {
return [e.offsetWidth, e.offsetHeight];
},
getRelMousePos : function(e) {
var x=0, y = 0;
if (!e) { e = window.event; }
if (typeof e.offsetX === 'number') {
x = e.offsetX;
y = e.offsetY;
} else if (typeof e.layerX === 'number') {
x = e.layerX;
y = e.layerY;
}
return { x: x, y: y };
},
getViewPos : function() {
if(typeof window.pageYOffset === 'number') {
return [window.pageXOffset, window.pageYOffset];
} else if(document.body && (document.body.scrollLeft || document.body.scrollTop)) {
return [document.body.scrollLeft, document.body.scrollTop];
} else if(document.documentElement && (document.documentElement.scrollLeft || document.documentElement.scrollTop)) {
return [document.documentElement.scrollLeft, document.documentElement.scrollTop];
} else {
return [0, 0];
}
},
getViewSize : function() {
if(typeof window.innerWidth === 'number') {
return [window.innerWidth, window.innerHeight];
} else if(document.body && (document.body.clientWidth || document.body.clientHeight)) {
return [document.body.clientWidth, document.body.clientHeight];
} else if(document.documentElement && (document.documentElement.clientWidth || document.documentElement.clientHeight)) {
return [document.documentElement.clientWidth, document.documentElement.clientHeight];
} else {
return [0, 0];
}
},
URI : function(uri) { // See RFC3986
this.scheme = null;
this.authority = null;
this.path = '';
this.query = null;
this.fragment = null;
this.parse = function(uri) {
var m=uri.match(/^(([A-Za-z][0-9A-Za-z+.-]*)(:))?((\/\/)([^\/?#]*))?([^?#]*)((\?)([^#]*))?((#)(.*))?/);
this.scheme = m[3] ? m[2] : null;
this.authority = m[5] ? m[6] : null;
this.path = m[7];
this.query = m[9] ? m[10] : null;
this.fragment = m[12] ? m[13] : null;
return this;
};
this.toString = function() {
var result='';
if(this.scheme !== null) { result = result + this.scheme + ':'; }
if(this.authority !== null) { result = result + '//' + this.authority; }
if(this.path !== null) { result = result + this.path; }
if(this.query !== null) { result = result + '?' + this.query; }
if(this.fragment !== null) { result = result + '#' + this.fragment; }
return result;
};
this.toAbsolute = function(base) {
var base=new jscolor.URI(base);
var r=this;
var t=new jscolor.URI;
if(base.scheme === null) { return false; }
if(r.scheme !== null && r.scheme.toLowerCase() === base.scheme.toLowerCase()) {
r.scheme = null;
}
if(r.scheme !== null) {
t.scheme = r.scheme;
t.authority = r.authority;
t.path = removeDotSegments(r.path);
t.query = r.query;
} else {
if(r.authority !== null) {
t.authority = r.authority;
t.path = removeDotSegments(r.path);
t.query = r.query;
} else {
if(r.path === '') { // TODO: == or === ?
t.path = base.path;
if(r.query !== null) {
t.query = r.query;
} else {
t.query = base.query;
}
} else {
if(r.path.substr(0,1) === '/') {
t.path = removeDotSegments(r.path);
} else {
if(base.authority !== null && base.path === '') { // TODO: == or === ?
t.path = '/'+r.path;
} else {
t.path = base.path.replace(/[^\/]+$/,'')+r.path;
}
t.path = removeDotSegments(t.path);
}
t.query = r.query;
}
t.authority = base.authority;
}
t.scheme = base.scheme;
}
t.fragment = r.fragment;
return t;
};
function removeDotSegments(path) {
var out='';
while(path) {
if(path.substr(0,3)==='../' || path.substr(0,2)==='./') {
path = path.replace(/^\.+/,'').substr(1);
} else if(path.substr(0,3)==='/./' || path==='/.') {
path = '/'+path.substr(3);
} else if(path.substr(0,4)==='/../' || path==='/..') {
path = '/'+path.substr(4);
out = out.replace(/\/?[^\/]*$/, '');
} else if(path==='.' || path==='..') {
path = '';
} else {
var rm=path.match(/^\/?[^\/]*/)[0];
path = path.substr(rm.length);
out = out + rm;
}
}
return out;
}
if(uri) {
this.parse(uri);
}
},
color : function(target, prop) {
this.required = true; // refuse empty values?
this.adjust = true; // adjust value to uniform notation?
this.hash = false; // prefix color with # symbol?
this.caps = true; // uppercase?
this.slider = true; // show the value/saturation slider?
this.valueElement = target; // value holder
this.styleElement = target; // where to reflect current color
this.onImmediateChange = null; // onchange callback (can be either string or function)
this.hsv = [0, 0, 1]; // read-only  0-6, 0-1, 0-1
this.rgb = [1, 1, 1]; // read-only  0-1, 0-1, 0-1
this.pickerOnfocus = true; // display picker on focus?
this.pickerMode = 'HSV'; // HSV | HVS
this.pickerPosition = 'bottom'; // left | right | top | bottom
this.pickerButtonHeight = 20; // px
this.pickerClosable = false;
this.pickerCloseText = 'Close';
this.pickerButtonColor = 'ButtonText'; // px
this.pickerFace = 10; // px
this.pickerFaceColor = 'ThreeDFace'; // CSS color
this.pickerBorder = 1; // px
this.pickerBorderColor = 'ThreeDHighlight ThreeDShadow ThreeDShadow ThreeDHighlight'; // CSS color
this.pickerInset = 1; // px
this.pickerInsetColor = 'ThreeDShadow ThreeDHighlight ThreeDHighlight ThreeDShadow'; // CSS color
this.pickerZIndex = 10000;
for(var p in prop) {
if(prop.hasOwnProperty(p)) {
this[p] = prop[p];
}
}
this.hidePicker = function() {
if(isPickerOwner()) {
removePicker();
}
};
this.showPicker = function() {
if(!isPickerOwner()) {
var tp=jscolor.getElementPos(target); // target pos
var ts=jscolor.getElementSize(target); // target size
var vp=jscolor.getViewPos(); // view pos
var vs=jscolor.getViewSize(); // view size
var ps=getPickerDims(this); // picker size
var a, b, c;
switch(this.pickerPosition.toLowerCase()) {
case 'left': a=1; b=0; c=-1; break;
case 'right':a=1; b=0; c=1; break;
case 'top':  a=0; b=1; c=-1; break;
default:     a=0; b=1; c=1; break;
}
var l=(ts[b]+ps[b])/2;
var pp=[ // picker pos
-vp[a]+tp[a]+ps[a] > vs[a] ?
(-vp[a]+tp[a]+ts[a]/2 > vs[a]/2 && tp[a]+ts[a]-ps[a] >= 0 ? tp[a]+ts[a]-ps[a] : tp[a]) :
tp[a],
-vp[b]+tp[b]+ts[b]+ps[b]-l+l*c > vs[b] ?
(-vp[b]+tp[b]+ts[b]/2 > vs[b]/2 && tp[b]+ts[b]-l-l*c >= 0 ? tp[b]+ts[b]-l-l*c : tp[b]+ts[b]-l+l*c) :
(tp[b]+ts[b]-l+l*c >= 0 ? tp[b]+ts[b]-l+l*c : tp[b]+ts[b]-l-l*c)
];
drawPicker(pp[a], pp[b]);
}
};
this.importColor = function() {
if(!valueElement) {
this.exportColor();
} else {
if(!this.adjust) {
if(!this.fromString(valueElement.value, leaveValue)) {
styleElement.style.backgroundColor = styleElement.jscStyle.backgroundColor;
styleElement.style.color = styleElement.jscStyle.color;
this.exportColor(leaveValue | leaveStyle);
}
} else if(!this.required && /^\s*$/.test(valueElement.value)) {
valueElement.value = '';
styleElement.style.backgroundColor = styleElement.jscStyle.backgroundColor;
styleElement.style.color = styleElement.jscStyle.color;
this.exportColor(leaveValue | leaveStyle);
} else if(this.fromString(valueElement.value)) {
} else {
this.exportColor();
}
}
};
this.exportColor = function(flags) {
if(!(flags & leaveValue) && valueElement) {
var value=this.toString();
if(this.caps) { value = value.toUpperCase(); }
if(this.hash) { value = '#'+value; }
valueElement.value = value;
}
if(!(flags & leaveStyle) && styleElement) {
styleElement.style.backgroundColor =
'#'+this.toString();
styleElement.style.color =
0.213 * this.rgb[0] +
0.715 * this.rgb[1] +
0.072 * this.rgb[2]
< 0.5 ? '#FFF' : '#000';
}
if(!(flags & leavePad) && isPickerOwner()) {
redrawPad();
}
if(!(flags & leaveSld) && isPickerOwner()) {
redrawSld();
}
};
this.fromHSV = function(h, s, v, flags) { // null = don't change
h<0 && (h=0) || h>6 && (h=6);
s<0 && (s=0) || s>1 && (s=1);
v<0 && (v=0) || v>1 && (v=1);
this.rgb = HSV_RGB(
h===null ? this.hsv[0] : (this.hsv[0]=h),
s===null ? this.hsv[1] : (this.hsv[1]=s),
v===null ? this.hsv[2] : (this.hsv[2]=v)
);
this.exportColor(flags);
};
this.fromRGB = function(r, g, b, flags) { // null = don't change
r<0 && (r=0) || r>1 && (r=1);
g<0 && (g=0) || g>1 && (g=1);
b<0 && (b=0) || b>1 && (b=1);
var hsv=RGB_HSV(
r===null ? this.rgb[0] : (this.rgb[0]=r),
g===null ? this.rgb[1] : (this.rgb[1]=g),
b===null ? this.rgb[2] : (this.rgb[2]=b)
);
if(hsv[0] !== null) {
this.hsv[0] = hsv[0];
}
if(hsv[2] !== 0) {
this.hsv[1] = hsv[1];
}
this.hsv[2] = hsv[2];
this.exportColor(flags);
};
this.fromString = function(hex, flags) {
var m=hex.match(/^\W*([0-9A-F]{3}([0-9A-F]{3})?)\W*$/i);
if(!m) {
return false;
} else {
if(m[1].length === 6) { // 6-char notation
this.fromRGB(
parseInt(m[1].substr(0,2),16) / 255,
parseInt(m[1].substr(2,2),16) / 255,
parseInt(m[1].substr(4,2),16) / 255,
flags
);
} else { // 3-char notation
this.fromRGB(
parseInt(m[1].charAt(0)+m[1].charAt(0),16) / 255,
parseInt(m[1].charAt(1)+m[1].charAt(1),16) / 255,
parseInt(m[1].charAt(2)+m[1].charAt(2),16) / 255,
flags
);
}
return true;
}
};
this.toString = function() {
return (
(0x100 | Math.round(255*this.rgb[0])).toString(16).substr(1) +
(0x100 | Math.round(255*this.rgb[1])).toString(16).substr(1) +
(0x100 | Math.round(255*this.rgb[2])).toString(16).substr(1)
);
};
function RGB_HSV(r, g, b) {
var n=Math.min(Math.min(r,g),b);
var v=Math.max(Math.max(r,g),b);
var m=v - n;
if(m === 0) { return [ null, 0, v ]; }
var h=r===n ? 3+(b-g)/m : (g===n ? 5+(r-b)/m : 1+(g-r)/m);
return [ h===6?0:h, m/v, v ];
}
function HSV_RGB(h, s, v) {
if(h === null) { return [ v, v, v ]; }
var i=Math.floor(h);
var f=i%2 ? h-i : 1-(h-i);
var m=v * (1 - s);
var n=v * (1 - s*f);
switch(i) {
case 6:
case 0: return [v,n,m];
case 1: return [n,v,m];
case 2: return [m,v,n];
case 3: return [m,n,v];
case 4: return [n,m,v];
case 5: return [v,m,n];
}
}
function removePicker() {
delete jscolor.picker.owner;
document.getElementsByTagName('body')[0].removeChild(jscolor.picker.boxB);
}
function drawPicker(x, y) {
if(!jscolor.picker) {
jscolor.picker = {
box : document.createElement('div'),
boxB : document.createElement('div'),
pad : document.createElement('div'),
padB : document.createElement('div'),
padM : document.createElement('div'),
sld : document.createElement('div'),
sldB : document.createElement('div'),
sldM : document.createElement('div'),
btn : document.createElement('div'),
btnS : document.createElement('span'),
btnT : document.createTextNode(THIS.pickerCloseText)
};
for(var i=0,segSize=4; i<jscolor.images.sld[1]; i+=segSize) {
var seg=document.createElement('div');
seg.style.height = segSize+'px';
seg.style.fontSize = '1px';
seg.style.lineHeight = '0';
jscolor.picker.sld.appendChild(seg);
}
jscolor.picker.sldB.appendChild(jscolor.picker.sld);
jscolor.picker.box.appendChild(jscolor.picker.sldB);
jscolor.picker.box.appendChild(jscolor.picker.sldM);
jscolor.picker.padB.appendChild(jscolor.picker.pad);
jscolor.picker.box.appendChild(jscolor.picker.padB);
jscolor.picker.box.appendChild(jscolor.picker.padM);
jscolor.picker.btnS.appendChild(jscolor.picker.btnT);
jscolor.picker.btn.appendChild(jscolor.picker.btnS);
jscolor.picker.box.appendChild(jscolor.picker.btn);
jscolor.picker.boxB.appendChild(jscolor.picker.box);
}
var p=jscolor.picker;
p.box.onmouseup =
p.box.onmouseout = function() { target.focus(); };
p.box.onmousedown = function() { abortBlur=true; };
p.box.onmousemove = function(e) {
if (holdPad || holdSld) {
holdPad && setPad(e);
holdSld && setSld(e);
if (document.selection) {
document.selection.empty();
} else if (window.getSelection) {
window.getSelection().removeAllRanges();
}
dispatchImmediateChange();
}
};
p.padM.onmouseup =
p.padM.onmouseout = function() { if(holdPad) { holdPad=false; jscolor.fireEvent(valueElement,'change'); } };
p.padM.onmousedown = function(e) {
holdPad=true;
setPad(e);
dispatchImmediateChange();
};
p.sldM.onmouseup =
p.sldM.onmouseout = function() { if(holdSld) { holdSld=false; jscolor.fireEvent(valueElement,'change'); } };
p.sldM.onmousedown = function(e) {
holdSld=true;
setSld(e);
dispatchImmediateChange();
};
var dims=getPickerDims(THIS);
p.box.style.width = dims[0] + 'px';
p.box.style.height = dims[1] + 'px';
p.boxB.style.position = 'absolute';
p.boxB.style.clear = 'both';
p.boxB.style.left = x+'px';
p.boxB.style.top = y+'px';
p.boxB.style.zIndex = THIS.pickerZIndex;
p.boxB.style.border = THIS.pickerBorder+'px solid';
p.boxB.style.borderColor = THIS.pickerBorderColor;
p.boxB.style.background = THIS.pickerFaceColor;
p.pad.style.width = jscolor.images.pad[0]+'px';
p.pad.style.height = jscolor.images.pad[1]+'px';
p.padB.style.position = 'absolute';
p.padB.style.left = THIS.pickerFace+'px';
p.padB.style.top = THIS.pickerFace+'px';
p.padB.style.border = THIS.pickerInset+'px solid';
p.padB.style.borderColor = THIS.pickerInsetColor;
p.padM.style.position = 'absolute';
p.padM.style.left = '0';
p.padM.style.top = '0';
p.padM.style.width = THIS.pickerFace + 2*THIS.pickerInset + jscolor.images.pad[0] + jscolor.images.arrow[0] + 'px';
p.padM.style.height = p.box.style.height;
p.padM.style.cursor = 'crosshair';
p.sld.style.overflow = 'hidden';
p.sld.style.width = jscolor.images.sld[0]+'px';
p.sld.style.height = jscolor.images.sld[1]+'px';
p.sldB.style.display = THIS.slider ? 'block' : 'none';
p.sldB.style.position = 'absolute';
p.sldB.style.right = THIS.pickerFace+'px';
p.sldB.style.top = THIS.pickerFace+'px';
p.sldB.style.border = THIS.pickerInset+'px solid';
p.sldB.style.borderColor = THIS.pickerInsetColor;
p.sldM.style.display = THIS.slider ? 'block' : 'none';
p.sldM.style.position = 'absolute';
p.sldM.style.right = '0';
p.sldM.style.top = '0';
p.sldM.style.width = jscolor.images.sld[0] + jscolor.images.arrow[0] + THIS.pickerFace + 2*THIS.pickerInset + 'px';
p.sldM.style.height = p.box.style.height;
try {
p.sldM.style.cursor = 'pointer';
} catch(eOldIE) {
p.sldM.style.cursor = 'hand';
}
function setBtnBorder() {
var insetColors=THIS.pickerInsetColor.split(/\s+/);
var pickerOutsetColor=insetColors.length < 2 ? insetColors[0] : insetColors[1] + ' ' + insetColors[0] + ' ' + insetColors[0] + ' ' + insetColors[1];
p.btn.style.borderColor = pickerOutsetColor;
}
p.btn.style.display = THIS.pickerClosable ? 'block' : 'none';
p.btn.style.position = 'absolute';
p.btn.style.left = THIS.pickerFace + 'px';
p.btn.style.bottom = THIS.pickerFace + 'px';
p.btn.style.padding = '0 15px';
p.btn.style.height = '18px';
p.btn.style.border = THIS.pickerInset + 'px solid';
setBtnBorder();
p.btn.style.color = THIS.pickerButtonColor;
p.btn.style.font = '12px sans-serif';
p.btn.style.textAlign = 'center';
try {
p.btn.style.cursor = 'pointer';
} catch(eOldIE) {
p.btn.style.cursor = 'hand';
}
p.btn.onmousedown = function () {
THIS.hidePicker();
};
p.btnS.style.lineHeight = p.btn.style.height;
switch(modeID) {
case 0: var padImg='hs.png'; break;
case 1: var padImg='hv.png'; break;
}
p.padM.style.backgroundImage = "url('"+jscolor.getDir()+"cross.gif')";
p.padM.style.backgroundRepeat = "no-repeat";
p.sldM.style.backgroundImage = "url('"+jscolor.getDir()+"arrow.gif')";
p.sldM.style.backgroundRepeat = "no-repeat";
p.pad.style.backgroundImage = "url('"+jscolor.getDir()+padImg+"')";
p.pad.style.backgroundRepeat = "no-repeat";
p.pad.style.backgroundPosition = "0 0";
redrawPad();
redrawSld();
jscolor.picker.owner = THIS;
document.getElementsByTagName('body')[0].appendChild(p.boxB);
}
function getPickerDims(o) {
var dims=[
2*o.pickerInset + 2*o.pickerFace + jscolor.images.pad[0] +
(o.slider ? 2*o.pickerInset + 2*jscolor.images.arrow[0] + jscolor.images.sld[0] : 0),
o.pickerClosable ?
4*o.pickerInset + 3*o.pickerFace + jscolor.images.pad[1] + o.pickerButtonHeight :
2*o.pickerInset + 2*o.pickerFace + jscolor.images.pad[1]
];
return dims;
}
function redrawPad() {
switch(modeID) {
case 0: var yComponent=1; break;
case 1: var yComponent=2; break;
}
var x=Math.round((THIS.hsv[0]/6) * (jscolor.images.pad[0]-1));
var y=Math.round((1-THIS.hsv[yComponent]) * (jscolor.images.pad[1]-1));
jscolor.picker.padM.style.backgroundPosition =
(THIS.pickerFace+THIS.pickerInset+x - Math.floor(jscolor.images.cross[0]/2)) + 'px ' +
(THIS.pickerFace+THIS.pickerInset+y - Math.floor(jscolor.images.cross[1]/2)) + 'px';
var seg=jscolor.picker.sld.childNodes;
switch(modeID) {
case 0:
var rgb=HSV_RGB(THIS.hsv[0], THIS.hsv[1], 1);
for(var i=0; i<seg.length; i+=1) {
seg[i].style.backgroundColor = 'rgb('+
(rgb[0]*(1-i/seg.length)*100)+'%,'+
(rgb[1]*(1-i/seg.length)*100)+'%,'+
(rgb[2]*(1-i/seg.length)*100)+'%)';
}
break;
case 1:
var rgb, s, c = [ THIS.hsv[2], 0, 0 ];
var i=Math.floor(THIS.hsv[0]);
var f=i%2 ? THIS.hsv[0]-i : 1-(THIS.hsv[0]-i);
switch(i) {
case 6:
case 0: rgb=[0,1,2]; break;
case 1: rgb=[1,0,2]; break;
case 2: rgb=[2,0,1]; break;
case 3: rgb=[2,1,0]; break;
case 4: rgb=[1,2,0]; break;
case 5: rgb=[0,2,1]; break;
}
for(var i=0; i<seg.length; i+=1) {
s = 1 - 1/(seg.length-1)*i;
c[1] = c[0] * (1 - s*f);
c[2] = c[0] * (1 - s);
seg[i].style.backgroundColor = 'rgb('+
(c[rgb[0]]*100)+'%,'+
(c[rgb[1]]*100)+'%,'+
(c[rgb[2]]*100)+'%)';
}
break;
}
}
function redrawSld() {
switch(modeID) {
case 0: var yComponent=2; break;
case 1: var yComponent=1; break;
}
var y=Math.round((1-THIS.hsv[yComponent]) * (jscolor.images.sld[1]-1));
jscolor.picker.sldM.style.backgroundPosition =
'0 ' + (THIS.pickerFace+THIS.pickerInset+y - Math.floor(jscolor.images.arrow[1]/2)) + 'px';
}
function isPickerOwner() {
return jscolor.picker && jscolor.picker.owner === THIS;
}
function blurTarget() {
if(valueElement === target) {
THIS.importColor();
}
if(THIS.pickerOnfocus) {
THIS.hidePicker();
}
}
function blurValue() {
if(valueElement !== target) {
THIS.importColor();
}
}
function setPad(e) {
var mpos=jscolor.getRelMousePos(e);
var x=mpos.x - THIS.pickerFace - THIS.pickerInset;
var y=mpos.y - THIS.pickerFace - THIS.pickerInset;
switch(modeID) {
case 0: THIS.fromHSV(x*(6/(jscolor.images.pad[0]-1)), 1 - y/(jscolor.images.pad[1]-1), null, leaveSld); break;
case 1: THIS.fromHSV(x*(6/(jscolor.images.pad[0]-1)), null, 1 - y/(jscolor.images.pad[1]-1), leaveSld); break;
}
}
function setSld(e) {
var mpos=jscolor.getRelMousePos(e);
var y=mpos.y - THIS.pickerFace - THIS.pickerInset;
switch(modeID) {
case 0: THIS.fromHSV(null, null, 1 - y/(jscolor.images.sld[1]-1), leavePad); break;
case 1: THIS.fromHSV(null, 1 - y/(jscolor.images.sld[1]-1), null, leavePad); break;
}
}
function dispatchImmediateChange() {
if (THIS.onImmediateChange) {
if (typeof THIS.onImmediateChange === 'string') {
eval(THIS.onImmediateChange);
} else {
THIS.onImmediateChange(THIS);
}
}
}
var THIS=this;
var modeID=this.pickerMode.toLowerCase()==='hvs' ? 1 : 0;
var abortBlur=false;
var
valueElement = jscolor.fetchElement(this.valueElement),
styleElement = jscolor.fetchElement(this.styleElement);
var
holdPad = false,
holdSld = false;
var
leaveValue = 1<<0,
leaveStyle = 1<<1,
leavePad = 1<<2,
leaveSld = 1<<3;
jscolor.addEvent(target, 'focus', function() {
if(THIS.pickerOnfocus) { THIS.showPicker(); }
});
jscolor.addEvent(target, 'blur', function() {
if(!abortBlur) {
window.setTimeout(function(){ abortBlur || blurTarget(); abortBlur=false; }, 0);
} else {
abortBlur = false;
}
});
if(valueElement) {
var updateField=function() {
THIS.fromString(valueElement.value, leaveValue);
};
jscolor.addEvent(valueElement, 'keyup', updateField);
jscolor.addEvent(valueElement, 'input', updateField);
jscolor.addEvent(valueElement, 'blur', blurValue);
valueElement.setAttribute('autocomplete', 'off');
}
if(styleElement) {
styleElement.jscStyle = {
backgroundColor : styleElement.style.backgroundColor,
color : styleElement.style.color
};
}
switch(modeID) {
case 0: jscolor.requireImage('hs.png'); break;
case 1: jscolor.requireImage('hv.png'); break;
}
jscolor.requireImage('cross.gif');
jscolor.requireImage('arrow.gif');
this.importColor();
}
};
jscolor.install();
