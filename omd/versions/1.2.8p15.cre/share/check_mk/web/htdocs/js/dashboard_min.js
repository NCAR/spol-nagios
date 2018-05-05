var reload_on_resize={};function size_dashlets(){var size_info=calculate_dashlets();var oDash=null;var oDashTitle=null;var oDashInner=null;var oDashControls=null;for(var d_number=0;d_number<size_info.length;d_number++){var dashlet=size_info[d_number];var d_left=dashlet[0];var d_top=dashlet[1];var d_width=dashlet[2];var d_height=dashlet[3];var disstyle="block";oDashTitle=document.getElementById("dashlet_title_"+d_number);var has_title=false;if(oDashTitle){has_title=true;if(d_width<=20)d_width=21;oDashTitle.style.width=(d_width-13)+"px";oDashTitle.style.display=disstyle;oDashTitle.style.left=dashlet_padding[3]+"px";oDashTitle.style.top=dashlet_padding[4]+"px";}oDash=document.getElementById("dashlet_"+d_number);if(oDash){oDash.style.display=disstyle;oDash.style.left=d_left+"px";oDash.style.top=d_top+"px";oDash.style.width=d_width+"px";oDash.style.height=d_height+"px";}var top_padding=dashlet_padding[0];if(!has_title)top_padding=dashlet_padding[4];var netto_height=d_height-top_padding-dashlet_padding[2];var netto_width=d_width-dashlet_padding[1]-dashlet_padding[3];oDashInner=document.getElementById("dashlet_inner_"+d_number);if(oDashInner){oDashInner.style.display=disstyle;var old_width=oDashInner.clientWidth;var old_height=oDashInner.clientHeight;oDashInner.style.left=dashlet_padding[3]+"px";oDashInner.style.top=top_padding+"px";if(netto_width>0)oDashInner.style.width=netto_width+"px";if(netto_height>0)oDashInner.style.height=netto_height+"px";if(old_width!=oDashInner.clientWidth||old_height!=oDashInner.clientHeight)if(!g_resizing||parseInt(g_resizing.parentNode.parentNode.id.replace('dashlet_',''))!=d_number)dashlet_resized(d_number,oDashInner);}oDashControls=document.getElementById("dashlet_controls_"+d_number);if(oDashControls)set_control_size(oDashControls,d_width,d_height);}oDash=null;oDashTitle=null;oDashInner=null;oDashControls=null;}function set_control_size(dash_controls,width,height){dash_controls.style.width=(width-dashlet_padding[1]-dashlet_padding[3])+"px";dash_controls.style.height=(height-dashlet_padding[2]-dashlet_padding[4])+"px";dash_controls.style.left=dashlet_padding[3]+"px";dash_controls.style.top=dashlet_padding[4]+"px";}function is_dynamic(x){return x==MAX||x==GROW;}function align_to_grid(px){return ~~(px/grid_size)*grid_size;}function vec(x,y){this.x=x||0;this.y=y||0;}vec.prototype={divide:function(s){return new vec(~~(this.x/s),~~(this.y/s));},add:function(v){return new vec(this.x+v.x,this.y+v.y);},make_absolute:function(size_v){return new vec(this.x<0?this.x+size_v.x+1:this.x-1,this.y<0?this.y+size_v.y+1:this.y-1);},initial_size:function(pos_v,grid_v){return new vec((this.x==MAX?grid_v.x-Math.abs(pos_v.x)+1:(this.x==GROW?dashlet_min_size[0]:this.x)),(this.y==MAX?grid_v.y-Math.abs(pos_v.y)+1:(this.y==GROW?dashlet_min_size[1]:this.y)));},compute_grow_by:function(size_v){return new vec((size_v.x!=GROW?0:(this.x<0?-1:1)),(size_v.y!=GROW?0:(this.y<0?-1:1)));},toString:function(){return this.x+'/'+this.y;}};function calculate_dashlets(){var screen_size=new vec(g_dashboard_width,g_dashboard_height);var raster_size=screen_size.divide(grid_size);var used_matrix={};var positions=[];for(var nr=0;nr<dashlets.length;nr++){var dashlet=dashlets[nr];var rel_position=new vec(dashlet.x,dashlet.y);var abs_position=rel_position.make_absolute(raster_size);var size=new vec(dashlet.w,dashlet.h);var used_size=size.initial_size(rel_position,raster_size);var top,left,right,bottom;if(rel_position.x>0){left=abs_position.x;right=left+used_size.x;}else{right=abs_position.x;left=right-used_size.x;}if(rel_position.y>0){top=abs_position.y;bottom=top+used_size.y;}else{bottom=abs_position.y;top=bottom-used_size.y;}for(var x=left;x<right;x++)for(var y=top;y<bottom;y++)used_matrix[x+' '+y]=true;var grow_by=rel_position.compute_grow_by(size);positions.push([left,top,right,bottom,grow_by]);}var try_allocate=function(left,top,right,bottom){for(var x=left;x<right;x++)for(var y=top;y<bottom;y++)if(x+' '+y in used_matrix)return false;for(var x=left;x<right;x++)for(var y=top;y<bottom;y++)used_matrix[x+' '+y]=true;return true;};var at_least_one_expanded=true;while(at_least_one_expanded){at_least_one_expanded=false;var new_positions=[];for(var nr=0;nr<positions.length;nr++){var left=positions[nr][0],top=positions[nr][1],right=positions[nr][2],bottom=positions[nr][3],grow_by=positions[nr][4];if(grow_by.x>0&&right<raster_size.x&&try_allocate(right,top,right+1,bottom)){at_least_one_expanded=true;right+=1;}else if(grow_by.x<0&&left>0&&try_allocate(left-1,top,left,bottom)){at_least_one_expanded=true;left-=1;}if(grow_by.y>0&&bottom<raster_size.y&&try_allocate(left,bottom,right,bottom+1)){at_least_one_expanded=true;bottom+=1;}else if(grow_by.y<0&&top>0&&try_allocate(left,top-1,right,top)){at_least_one_expanded=true;top-=1;}new_positions.push([left,top,right,bottom,grow_by]);}positions=new_positions;}var size_info=[];for(var nr=0;nr<positions.length;nr++){var left=positions[nr][0],top=positions[nr][1],right=positions[nr][2],bottom=positions[nr][3];size_info.push([left*grid_size,top*grid_size,(right-left)*grid_size,(bottom-top)*grid_size]);}return size_info;}var g_dashboard_resizer=null;var g_dashboard_top=null;var g_dashboard_left=null;var g_dashboard_width=null;var g_dashboard_height=null;function calculate_dashboard(){if(g_dashboard_resizer!==null)return;g_dashboard_resizer=true;g_dashboard_top=header_height+screen_margin;g_dashboard_left=screen_margin;g_dashboard_width=pageWidth()-2*screen_margin;g_dashboard_height=pageHeight()-2*screen_margin-header_height;var oDash=document.getElementById("dashboard");oDash.style.left=g_dashboard_left+"px";oDash.style.top=g_dashboard_top+"px";oDash.style.width=g_dashboard_width+"px";oDash.style.height=g_dashboard_height+"px";size_dashlets();g_dashboard_resizer=null;}function dashboard_scheduler(initial){var timestamp=Date.parse(new Date())/1000;var newcontent="";for(var i=0;i<refresh_dashlets.length;i++){var nr=refresh_dashlets[i][0];var refresh=refresh_dashlets[i][1];var url=refresh_dashlets[i][2];if((initial&&document.getElementById("dashlet_inner_"+nr).innerHTML=='')||(refresh>0&&timestamp%refresh==0))if(typeof url==='string'){if(url.indexOf('\?')!==-1)url+="&mtime="+dashboard_mtime;else url+="?mtime="+dashboard_mtime;get_url(url,dashboard_update_contents,"dashlet_inner_"+nr);}else url();}if(timestamp%60==0)update_header_timer();g_reload_timer=setTimeout(function(){dashboard_scheduler(0);},1000);}function dashboard_update_contents(id,response_text){update_header_timer();updateContents(id,response_text);}function update_dashlet(id,code){var obj=document.getElementById(id);if(obj){obj.innerHTML=code;executeJS(id);obj=null;}}function toggle_dashboard_menu(show,event){var controls=document.getElementById('controls');if(!controls)return;if(typeof show==='undefined')var show=controls.style.display=='none';if(show){controls.style.display='block';hide_submenus();if(event){var target=getTarget(event);controls.style.left=(event.clientX-target.offsetLeft+5)+'px';controls.style.top=(event.clientY-target.offsetTop+5)+'px';var dashboard=document.getElementById('dashboard');if(controls.offsetLeft+controls.clientWidth>dashboard.clientWidth)controls.style.left=(controls.offsetLeft-controls.clientWidth-15)+'px';if(controls.offsetTop+controls.clientHeight>dashboard.clientHeight){var new_top=controls.offsetTop-controls.clientHeight-5;if(target!=dashboard)new_top-=dashboard.offsetTop;controls.style.top=new_top+'px';}}}else controls.style.display='none';}function hide_submenus(){var subs=document.getElementsByClassName('sub');for(var i=0;i<subs.length;i++)subs[i].style.display='none';}function show_submenu(id){document.getElementById(id+'_sub').style.display='block';}var g_editing=false;function toggle_dashboard_edit(){toggle_dashboard_menu(false);g_editing=!g_editing;document.getElementById('control_edit').style.display=!g_editing?'block':'none';document.getElementById('control_add').style.display=g_editing?'block':'none';document.getElementById('control_view').style.display=g_editing?'block':'none';var dashlet_divs=document.getElementsByClassName('dashlet');for(var i=0;i<dashlet_divs.length;i++)dashlet_toggle_edit(dashlet_divs[i]);if(window.parent.history.replaceState){var url=window.parent.location.href;if(url.indexOf("start_url")!==-1){var frame_url=decodeURIComponent(getUrlParam("start_url",url));frame_url=makeuri({'edit':g_editing?'1':'0'},frame_url);new_url=makeuri({'start_url':frame_url},url);}else new_url=makeuri({'edit':g_editing?'1':'0'},url);window.parent.history.replaceState({},document.title,new_url);}toggle_grid();}function toggle_grid(){if(!g_editing)remove_class(document.getElementById('dashboard'),'grid');else add_class(document.getElementById('dashboard'),'grid');}function render_resize_controls(controls,i){for(var a=0;a<2;a++){var resize=document.createElement('div');resize.className='resize resize'+i+' resize'+i+'_'+a;controls.appendChild(resize);}}function render_sizer(controls,nr,i,anchor_id,size){var sizer=document.createElement('div');sizer.className='sizer sizer'+i+' anchor'+anchor_id;var sizer_lbl=document.createElement('div');sizer_lbl.className='sizer_lbl sizer_lbl'+i+' anchor'+anchor_id;if(size==MAX){sizer.className+=' max';sizer.title='Use maximum available space in this direction';}else if(size==GROW){sizer.className+=' grow';sizer.title='Grow in this direction';}else{sizer.className+=' abs';sizer.title='Fixed size (drag border for resize)';render_resize_controls(controls,i);}sizer.onclick=function(dashlet_id,sizer_id){return function(){toggle_sizer(dashlet_id,sizer_id);};}(nr,i);sizer_lbl.onclick=sizer.onclick;sizer_lbl.title=sizer.title;controls.appendChild(sizer);if(is_dynamic(size))controls.appendChild(sizer_lbl);}function render_corner_resizers(controls,dashlet_id){for(var corner_id=0;corner_id<4;corner_id++){var resize=document.createElement('div');resize.className='resize resize_corner resize_corner'+corner_id;controls.appendChild(resize);}}function dashlet_toggle_edit(dashlet_obj,edit){var nr=parseInt(dashlet_obj.id.replace('dashlet_',''));var inner=document.getElementById('dashlet_inner_'+nr);var dashlet=dashlets[nr];var edit=edit===undefined?g_editing:edit;if(edit){add_class(dashlet_obj,'edit');var controls=document.createElement('div');controls.setAttribute('id','dashlet_controls_'+nr);controls.className='controls';dashlet_obj.appendChild(controls);set_control_size(controls,dashlet_obj.clientWidth,dashlet_obj.clientHeight);if(is_ie_below_9())controls.style.background='url(about:blank)';var anchor_id=get_anchor_id(dashlet);if(has_class(dashlet_obj,'resizable')){for(var i=0;i<2;i++)if(i==0)render_sizer(controls,nr,i,anchor_id,dashlet.w);else render_sizer(controls,nr,i,anchor_id,dashlet.h);if(!is_dynamic(dashlet.w)&&!is_dynamic(dashlet.h))render_corner_resizers(controls,nr);}for(var i=0;i<4;i++){var anchor=document.createElement('a');anchor.className='anchor anchor'+i;anchor.title='Currently growing from here';if(anchor_id!=i){anchor.className+=' off';anchor.title='Click to start growing from here';}anchor.onclick=function(dashlet_id,anchor_id){return function(){toggle_anchor(dashlet_id,anchor_id);};}(nr,i);controls.appendChild(anchor);}var edit=document.createElement('a');edit.className='edit';edit.title='Edit properties of this dashlet';edit.onclick=function(dashlet_id,board_name){return function(){location.href='edit_dashlet.py?name='+board_name+'&id='+dashlet_id;};}(nr,dashboard_name);controls.appendChild(edit);var del=document.createElement('a');del.className='del';del.title='Delete this dashlet';del.onclick=function(dashlet_id,board_name){return function(){location.href='delete_dashlet.py?name='+board_name+'&id='+dashlet_id;};}(nr,dashboard_name);controls.appendChild(del);}else{remove_class(dashlet_obj,'edit');var controls=document.getElementById('dashlet_controls_'+nr);controls.parentNode.removeChild(controls);}}var g_last_absolute_widths={};var g_last_absolute_heights={};function toggle_sizer(nr,sizer_id){var dashlet=dashlets[nr];var dashlet_obj=document.getElementById('dashlet_'+nr);if(sizer_id==0){if(dashlet.w>0){g_last_absolute_widths[nr]=dashlet.w;dashlet.w=GROW;}else if(dashlet.w==GROW){if(!(nr in g_last_absolute_widths))g_last_absolute_widths[nr]=dashlet_obj.clientWidth/grid_size;dashlet.w=MAX;}else if(dashlet.w==MAX)if(nr in g_last_absolute_widths)dashlet.w=g_last_absolute_widths[nr];else dashlet.w=dashlet_obj.clientWidth/grid_size;}else if(dashlet.h>0){g_last_absolute_heights[nr]=dashlet.h;dashlet.h=GROW;}else if(dashlet.h==GROW){if(!(nr in g_last_absolute_heights))g_last_absolute_heights[nr]=dashlet_obj.clientHeight/grid_size;dashlet.h=MAX;}else if(dashlet.h==MAX)if(nr in g_last_absolute_heights)dashlet.h=g_last_absolute_heights[nr];else dashlet.h=dashlet_obj.clientHeight/grid_size;rerender_dashlet_controls(dashlet_obj);size_dashlets();persist_dashlet_pos(nr);}var A_TOP_LEFT=0;var A_TOP_RIGHT=1;var A_BOTTOM_RIGHT=2;var A_BOTTOM_LEFT=3;function get_anchor_id(dashlet){var anchor_id;if(dashlet.x>0&&dashlet.y>0)anchor_id=A_TOP_LEFT;else if(dashlet.x<=0&&dashlet.y>0)anchor_id=A_TOP_RIGHT;else if(dashlet.x<=0&&dashlet.y<=0)anchor_id=A_BOTTOM_RIGHT;else if(dashlet.x>0&&dashlet.y<=0)anchor_id=A_BOTTOM_LEFT;return anchor_id;}function toggle_anchor(nr,anchor_id){if(anchor_id==get_anchor_id(dashlets[nr]))return;calculate_relative_dashlet_coords(nr,anchor_id);rerender_dashlet_controls(document.getElementById('dashlet_'+nr));size_dashlets();persist_dashlet_pos(nr);}function calculate_relative_dashlet_coords(nr,anchor_id){var dashlet=dashlets[nr];if(anchor_id===undefined)var anchor_id=get_anchor_id(dashlet);var dashlet_obj=document.getElementById('dashlet_'+nr);var x=dashlet_obj.offsetLeft/grid_size;var y=dashlet_obj.offsetTop/grid_size;var w=dashlet_obj.clientWidth/grid_size;var h=dashlet_obj.clientHeight/grid_size;var screen_size=new vec(g_dashboard_width,g_dashboard_height);var raster_size=screen_size.divide(grid_size);if(!is_dynamic(dashlet.w))dashlet.w=w;if(!is_dynamic(dashlet.h))dashlet.h=h;if(anchor_id==A_TOP_LEFT){dashlet.x=x;dashlet.y=y;}else if(anchor_id==A_TOP_RIGHT){dashlet.x=(x+w)-(raster_size.x+2);dashlet.y=y;}else if(anchor_id==A_BOTTOM_RIGHT){dashlet.x=(x+w)-(raster_size.x+2);dashlet.y=(y+h)-(raster_size.y+2);}else if(anchor_id==A_BOTTOM_LEFT){dashlet.x=x;dashlet.y=(y+h)-(raster_size.y+2);}dashlet.x+=1;dashlet.y+=1;}function rerender_dashlet_controls(dashlet_obj){dashlet_toggle_edit(dashlet_obj,false);dashlet_toggle_edit(dashlet_obj,true);}function body_click_handler(event){if(!event)event=window.event;var target=getTarget(event);var button=getButton(event);if(target.id=='dashboard'&&button=='RIGHT'){toggle_dashboard_menu(undefined,event);prevent_default_events(event);return false;}else if(target.parentNode.id=='controls_toggle'&&button=='LEFT'){toggle_dashboard_menu(undefined,event);prevent_default_events(event);return false;}else if(target.parentNode.id!='controls_toggle'&&(!target.parentNode.parentNode||!has_class(target.parentNode.parentNode,'menu')))toggle_dashboard_menu(false);return true;}var g_dragging=false;var g_drag_start=null;function drag_dashlet_start(event){if(!event)event=window.event;if(!g_editing)return true;var target=getTarget(event);var button=getButton(event);if(g_dragging===false&&button=='LEFT'&&has_class(target,'controls')){g_dragging=target.parentNode;var nr=parseInt(g_dragging.id.replace('dashlet_',''));var dashlet=dashlets[nr];var min_w=dashlet_min_size[0]*grid_size;var min_h=dashlet_min_size[1]*grid_size;var x=g_dragging.offsetLeft;var y=g_dragging.offsetTop;var w=g_dragging.clientWidth;var h=g_dragging.clientHeight;var anchor_id=get_anchor_id(dashlet);if(anchor_id==A_TOP_LEFT){if(is_dynamic(dashlet.w))w=min_w;if(is_dynamic(dashlet.h))h=min_h;}else if(anchor_id==A_TOP_RIGHT){if(is_dynamic(dashlet.w)){x=x+w-min_w;w=min_w;}if(is_dynamic(dashlet.h))h=min_h;}else if(anchor_id==A_BOTTOM_RIGHT){if(is_dynamic(dashlet.w)){x=x+w-min_w;w=min_w;}if(is_dynamic(dashlet.h)){y=y+h-min_h;h=min_h;}}else if(anchor_id==A_BOTTOM_LEFT){if(is_dynamic(dashlet.w))w=min_w;if(is_dynamic(dashlet.h)){y=y+h-min_h;h=min_h;}}g_drag_start={'m_x':event.clientX-g_dashboard_left,'m_y':event.clientY-g_dashboard_top,'x':x,'y':y,'w':w,'h':h};edit_visualize(g_dragging,true);prevent_default_events(event);return false;}return true;}function drag_dashlet(event){if(!event)event=window.event;var mouse_x=event.clientX-g_dashboard_left;var mouse_y=event.clientY-g_dashboard_top;if(!g_dragging)return true;var nr=parseInt(g_dragging.id.replace('dashlet_',''));var dashlet_obj=g_dragging;var diff_x=align_to_grid(g_drag_start.m_x-mouse_x);var diff_y=align_to_grid(g_drag_start.m_y-mouse_y);var x=g_drag_start.x-diff_x;var y=g_drag_start.y-diff_y;var w=g_drag_start.w;var h=g_drag_start.h;var board_w=align_to_grid(g_dashboard_width);var board_h=align_to_grid(g_dashboard_height);if(x<0){dashlet_obj.style.left='0px';dashlet_obj.style.width=w+'px';}else if(x+w>board_w){dashlet_obj.style.left=(board_w-w)+'px';dashlet_obj.style.width=w+'px';}else{dashlet_obj.style.left=x+'px';dashlet_obj.style.width=w+'px';}if(y<0){dashlet_obj.style.top='0px';dashlet_obj.style.height=h+'px';}else if(y+h>board_h){dashlet_obj.style.top=(board_h-h)+'px';dashlet_obj.style.height=h+'px';}else{dashlet_obj.style.top=y+'px';dashlet_obj.style.height=h+'px';}calculate_relative_dashlet_coords(nr);size_dashlets();}function drag_dashlet_stop(event){if(!event)event=window.event;if(!g_dragging)return true;edit_visualize(g_dragging,false);var nr=parseInt(g_dragging.id.replace('dashlet_',''));g_dragging=false;g_drag_start=null;persist_dashlet_pos(nr);return false;}function persist_dashlet_pos(nr){get_url('ajax_dashlet_pos.py?name='+dashboard_name+'&id='+nr+'&x='+dashlets[nr].x+'&y='+dashlets[nr].y+'&w='+dashlets[nr].w+'&h='+dashlets[nr].h,handle_dashlet_post_response,null,undefined,false);}function handle_dashlet_post_response(_unused,response_text){var parts=response_text.split(' ');if(parts[0]!='OK')alert('Error: '+response_text);else dashboard_mtime=parseInt(parts[1]);}function edit_visualize(obj,show){if(show)obj.style.zIndex=80;else obj.style.zIndex=1;}var g_resizing=false;var g_resize_start=null;function resize_dashlet_start(event){if(!event)event=window.event;if(!g_editing)return true;var target=getTarget(event);var button=getButton(event);if(g_resizing===false&&button=='LEFT'&&has_class(target,'resize')){var dashlet_obj=target.parentNode.parentNode;var nr=parseInt(dashlet_obj.id.replace('dashlet_',''));g_resizing=target;g_resize_start={'m_x':event.clientX,'m_y':event.clientY,'x':dashlet_obj.offsetLeft,'y':dashlet_obj.offsetTop,'w':dashlet_obj.clientWidth,'h':dashlet_obj.clientHeight};edit_visualize(dashlet_obj,true);prevent_default_events(event);return false;}return true;}function get_horizontal_direction(resizer){if(has_class(resizer,'resize0_0')||has_class(resizer,'resize_corner0')||has_class(resizer,'resize_corner3'))return 'left';else if(has_class(resizer,'resize0_1')||has_class(resizer,'resize_corner1')||has_class(resizer,'resize_corner2'))return 'right';}function get_vertical_direction(resizer){if(has_class(resizer,'resize1_0')||has_class(resizer,'resize_corner0')||has_class(resizer,'resize_corner1'))return 'top';else if(has_class(resizer,'resize1_1')||has_class(resizer,'resize_corner2')||has_class(resizer,'resize_corner3'))return 'bottom';}function resize_dashlet(event){if(!event)event=window.event;if(!g_resizing)return true;var dashlet_obj=g_resizing.parentNode.parentNode;var nr=parseInt(dashlet_obj.id.replace('dashlet_',''));var diff_x=align_to_grid(Math.abs(g_resize_start.m_x-event.clientX));var diff_y=align_to_grid(Math.abs(g_resize_start.m_y-event.clientY));if(event.clientX>g_resize_start.m_x)diff_x*=-1;if(event.clientY>g_resize_start.m_y)diff_y*=-1;var board_w=align_to_grid(g_dashboard_width);var board_h=align_to_grid(g_dashboard_height);var min_w=dashlet_min_size[0]*grid_size;var min_h=dashlet_min_size[1]*grid_size;if(get_horizontal_direction(g_resizing)=='left'){var new_x=g_resize_start.x-diff_x;if(new_x<0){dashlet_obj.style.left='0px';dashlet_obj.style.width=(g_resize_start.w+g_resize_start.x)+'px';}else if(g_resize_start.w+diff_x<min_w)dashlet_obj.style.width=min_w+'px';else{dashlet_obj.style.left=new_x+'px';dashlet_obj.style.width=(g_resize_start.w+diff_x)+'px';}}else if(get_horizontal_direction(g_resizing)=='right')if(g_resize_start.x+g_resize_start.w-diff_x>board_w)dashlet_obj.style.width=(board_w-g_resize_start.x)+'px';else if(g_resize_start.w-diff_x<min_w)dashlet_obj.style.width=min_w+'px';else dashlet_obj.style.width=(g_resize_start.w-diff_x)+'px';if(get_vertical_direction(g_resizing)=='top'){var new_y=g_resize_start.y-diff_y;if(new_y<0){dashlet_obj.style.top='0px';dashlet_obj.style.height=(g_resize_start.h+g_resize_start.y)+'px';}else if(g_resize_start.h+diff_y<min_h)dashlet_obj.style.height=min_h+'px';else{dashlet_obj.style.top=new_y+'px';dashlet_obj.style.height=(g_resize_start.h+diff_y)+'px';}}else if(get_vertical_direction(g_resizing)=='bottom')if(g_resize_start.y+g_resize_start.h-diff_y>=board_h)dashlet_obj.style.height=(board_h-g_resize_start.y)+'px';else if(g_resize_start.h-diff_y<min_h)dashlet_obj.style.height=min_h+'px';else dashlet_obj.style.height=(g_resize_start.h-diff_y)+'px';calculate_relative_dashlet_coords(nr);size_dashlets();}function resize_dashlet_stop(event){if(!event)event=window.event;if(!g_resizing)return true;var dashlet_obj=g_resizing.parentNode.parentNode;var nr=parseInt(dashlet_obj.id.replace('dashlet_',''));edit_visualize(dashlet_obj,false);g_resizing=false;dashlet_resized(nr,dashlet_obj);persist_dashlet_pos(nr);return false;}function dashlet_resized(nr,dashlet_obj){if(typeof reload_on_resize[nr]!='undefined'){var base_url=reload_on_resize[nr];var iframe=document.getElementById("dashlet_iframe_"+nr);iframe.src=base_url+'&width='+dashlet_obj.clientWidth+'&height='+dashlet_obj.clientHeight;iframe=null;}if(typeof on_resize_dashlets[nr]!='undefined')on_resize_dashlets[nr]();}add_event_handler('mousemove',function(e){return drag_dashlet(e)&&resize_dashlet(e);});add_event_handler('mousedown',function(e){return drag_dashlet_start(e)&&resize_dashlet_start(e);});add_event_handler('mouseup',function(e){return drag_dashlet_stop(e)&&resize_dashlet_stop(e);});add_event_handler('click',function(e){return body_click_handler(e);});add_event_handler('contextmenu',function(e){prevent_default_events(e);return false;});