import React from 'react'
import  api  from './api'
import apps  from './apps'
import  code  from './code'
import  dashboard  from './dashboard'
import  home  from './home'
import  info  from './info'
import  language  from './language'
import  list  from './list'
import  mail  from './mail'
import  mediation  from './mediation'
import  message  from './message'
import  perm_identity  from './perm_identity'
import  post_add  from './post_add'
import  radio_button_checked  from './radio_button_checked'
import  room  from './room'
import  settings  from './settings'
import  expand_more from './expand_more';
import  expand_less from './expand_less';

const iconTypes: any = {
    api,
    apps,
    code,
    dashboard,
    home,
    info,
    language,
    list,
    mail,
    mediation,
    message,
    perm_identity,
    post_add,
    radio_button_checked,
    room,
    settings,
    expand_less,
    expand_more
}

interface IconComponentProps {
    name: string
    height?: number
    width?: number
    fill?: string
    className?: string
    style?: any
}

const IconComponent = (props: IconComponentProps) => {
    let Icon = iconTypes[props.name]
    return <Icon className={props.className} {...props} />
}

 export default IconComponent
