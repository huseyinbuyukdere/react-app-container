import React from 'react'
import  api  from './api.svg'
import apps  from './apps.svg'
import  code  from './code.svg'
import  dashboard  from './dashboard.svg'
import  home  from './home.svg'
import  info  from './info.svg'
import  language  from './language.svg'
import  list  from './list.svg'
import  mail  from './mail.svg'
import  mediation  from './mediation.svg'
import  message  from './message.svg'
import  perm_identity  from './perm_identity.svg'
import  post_add  from './post_add.svg'
import  radio_button_checked  from './radio_button_checked.svg'
import  room  from './room.svg'
import  settings  from './settings.svg'
import  expand_more from './expand_more.svg';
import  expand_less from './expand_less.svg';

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
